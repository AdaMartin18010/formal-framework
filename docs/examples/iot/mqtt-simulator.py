#!/usr/bin/env python3
"""
MQTT设备模拟器
用于模拟IoT设备发送数据到EMQX MQTT Broker
"""

import paho.mqtt.client as mqtt
import json
import time
import random
import threading
import os
import signal
import sys
from datetime import datetime
from typing import Dict, Any

class MQTTDeviceSimulator:
    def __init__(self, broker_host: str = "localhost", broker_port: int = 1883):
        self.broker_host = broker_host
        self.broker_port = broker_port
        self.client = None
        self.devices = []
        self.running = False
        
    def on_connect(self, client, userdata, flags, rc):
        """连接回调"""
        if rc == 0:
            print(f"✅ 成功连接到MQTT Broker: {self.broker_host}:{self.broker_port}")
        else:
            print(f"❌ 连接失败，错误代码: {rc}")
    
    def on_disconnect(self, client, userdata, rc):
        """断开连接回调"""
        if rc != 0:
            print(f"⚠️  意外断开连接，错误代码: {rc}")
        else:
            print("🔌 正常断开连接")
    
    def on_publish(self, client, userdata, mid):
        """发布消息回调"""
        print(f"📤 消息已发布，消息ID: {mid}")
    
    def create_device(self, device_id: str, device_type: str) -> Dict[str, Any]:
        """创建设备配置"""
        device_configs = {
            "temperature_sensor": {
                "sensors": ["temperature", "humidity"],
                "ranges": {
                    "temperature": (15.0, 35.0),
                    "humidity": (30.0, 80.0)
                },
                "units": {
                    "temperature": "°C",
                    "humidity": "%"
                }
            },
            "pressure_sensor": {
                "sensors": ["pressure", "altitude"],
                "ranges": {
                    "pressure": (950.0, 1050.0),
                    "altitude": (0.0, 1000.0)
                },
                "units": {
                    "pressure": "hPa",
                    "altitude": "m"
                }
            },
            "motion_sensor": {
                "sensors": ["motion", "light"],
                "ranges": {
                    "motion": (0, 1),
                    "light": (0, 1000)
                },
                "units": {
                    "motion": "boolean",
                    "light": "lux"
                }
            },
            "air_quality": {
                "sensors": ["pm2_5", "pm10", "co2", "voc"],
                "ranges": {
                    "pm2_5": (0, 100),
                    "pm10": (0, 150),
                    "co2": (300, 2000),
                    "voc": (0, 500)
                },
                "units": {
                    "pm2_5": "μg/m³",
                    "pm10": "μg/m³",
                    "co2": "ppm",
                    "voc": "ppb"
                }
            }
        }
        
        config = device_configs.get(device_type, device_configs["temperature_sensor"])
        
        return {
            "device_id": device_id,
            "device_type": device_type,
            "sensors": config["sensors"],
            "ranges": config["ranges"],
            "units": config["units"],
            "location": {
                "latitude": round(random.uniform(39.9, 40.1), 6),
                "longitude": round(random.uniform(116.3, 116.5), 6)
            },
            "battery_level": random.randint(20, 100),
            "signal_strength": random.randint(-80, -30)
        }
    
    def generate_sensor_data(self, device: Dict[str, Any]) -> Dict[str, Any]:
        """生成传感器数据"""
        data = {
            "device_id": device["device_id"],
            "device_type": device["device_type"],
            "timestamp": datetime.utcnow().isoformat() + "Z",
            "location": device["location"],
            "battery_level": device["battery_level"],
            "signal_strength": device["signal_strength"],
            "sensors": {}
        }
        
        for sensor in device["sensors"]:
            min_val, max_val = device["ranges"][sensor]
            if device["units"][sensor] == "boolean":
                value = random.choice([0, 1])
            else:
                value = round(random.uniform(min_val, max_val), 2)
            
            data["sensors"][sensor] = {
                "value": value,
                "unit": device["units"][sensor]
            }
        
        return data
    
    def publish_device_data(self, device: Dict[str, Any]):
        """发布设备数据"""
        topic = f"devices/{device['device_type']}/{device['device_id']}/data"
        data = self.generate_sensor_data(device)
        
        message = json.dumps(data, indent=2)
        result = self.client.publish(topic, message, qos=1)
        
        if result.rc == mqtt.MQTT_ERR_SUCCESS:
            print(f"📡 设备 {device['device_id']} 数据已发布到主题: {topic}")
        else:
            print(f"❌ 设备 {device['device_id']} 数据发布失败")
    
    def device_worker(self, device: Dict[str, Any], interval: float):
        """设备工作线程"""
        while self.running:
            try:
                self.publish_device_data(device)
                time.sleep(interval)
            except Exception as e:
                print(f"❌ 设备 {device['device_id']} 发生错误: {e}")
                time.sleep(interval)
    
    def start_simulation(self, device_count: int = 5, message_interval: float = 5.0):
        """开始模拟"""
        print(f"🚀 启动MQTT设备模拟器")
        print(f"📊 设备数量: {device_count}")
        print(f"⏱️  消息间隔: {message_interval} 秒")
        
        # 创建MQTT客户端
        self.client = mqtt.Client()
        self.client.on_connect = self.on_connect
        self.client.on_disconnect = self.on_disconnect
        self.client.on_publish = self.on_publish
        
        try:
            # 连接到MQTT Broker
            self.client.connect(self.broker_host, self.broker_port, 60)
            self.client.loop_start()
            
            # 等待连接建立
            time.sleep(2)
            
            # 创建设备
            device_types = ["temperature_sensor", "pressure_sensor", "motion_sensor", "air_quality"]
            for i in range(device_count):
                device_type = random.choice(device_types)
                device_id = f"device_{i+1:03d}"
                device = self.create_device(device_id, device_type)
                self.devices.append(device)
            
            print(f"✅ 已创建 {len(self.devices)} 个设备")
            
            # 启动设备工作线程
            self.running = True
            threads = []
            
            for device in self.devices:
                thread = threading.Thread(
                    target=self.device_worker,
                    args=(device, message_interval)
                )
                thread.daemon = True
                thread.start()
                threads.append(thread)
            
            print("🎯 所有设备已启动，开始发送数据...")
            print("按 Ctrl+C 停止模拟")
            
            # 主循环
            while self.running:
                time.sleep(1)
                
        except KeyboardInterrupt:
            print("\n🛑 收到停止信号，正在关闭模拟器...")
            self.stop_simulation()
        except Exception as e:
            print(f"❌ 模拟器发生错误: {e}")
            self.stop_simulation()
    
    def stop_simulation(self):
        """停止模拟"""
        self.running = False
        
        if self.client:
            self.client.loop_stop()
            self.client.disconnect()
        
        print("✅ 模拟器已停止")
    
    def publish_device_status(self, device: Dict[str, Any], status: str):
        """发布设备状态"""
        topic = f"devices/{device['device_type']}/{device['device_id']}/status"
        status_data = {
            "device_id": device["device_id"],
            "status": status,
            "timestamp": datetime.utcnow().isoformat() + "Z",
            "battery_level": device["battery_level"],
            "signal_strength": device["signal_strength"]
        }
        
        message = json.dumps(status_data, indent=2)
        result = self.client.publish(topic, message, qos=1)
        
        if result.rc == mqtt.MQTT_ERR_SUCCESS:
            print(f"📊 设备 {device['device_id']} 状态已发布: {status}")
        else:
            print(f"❌ 设备 {device['device_id']} 状态发布失败")

def signal_handler(sig, frame):
    """信号处理器"""
    print("\n🛑 收到中断信号，正在退出...")
    sys.exit(0)

def main():
    # 注册信号处理器
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    
    # 从环境变量获取配置
    broker_host = os.getenv("MQTT_BROKER", "localhost")
    broker_port = int(os.getenv("MQTT_PORT", "1883"))
    device_count = int(os.getenv("DEVICE_COUNT", "5"))
    message_interval = float(os.getenv("MESSAGE_INTERVAL", "5.0"))
    
    print("=" * 50)
    print("🌐 MQTT设备模拟器")
    print("=" * 50)
    print(f"🔗 MQTT Broker: {broker_host}:{broker_port}")
    print(f"📱 设备数量: {device_count}")
    print(f"⏱️  消息间隔: {message_interval} 秒")
    print("=" * 50)
    
    # 创建并启动模拟器
    simulator = MQTTDeviceSimulator(broker_host, broker_port)
    
    try:
        simulator.start_simulation(device_count, message_interval)
    except Exception as e:
        print(f"❌ 启动失败: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
