import os, time
import paho.mqtt.client as mqtt

host = os.getenv('MQTT_HOST', '127.0.0.1')
port = int(os.getenv('MQTT_PORT', '1883'))
topic = os.getenv('MQTT_TOPIC', 'sensors/temperature')

client = mqtt.Client()
client.connect(host, port, 60)

for i in range(10):
    payload = f'{20 + i * 0.1:.2f}'
    client.publish(topic, payload)
    print('pub', topic, payload)
    time.sleep(1)

client.disconnect()
