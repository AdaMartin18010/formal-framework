import os
import paho.mqtt.client as mqtt

host = os.getenv('MQTT_HOST', '127.0.0.1')
port = int(os.getenv('MQTT_PORT', '1883'))
topic = os.getenv('MQTT_TOPIC', 'sensors/temperature')

client = mqtt.Client()

def on_connect(client, userdata, flags, rc):
    client.subscribe(topic)

def on_message(client, userdata, msg):
    print('sub', msg.topic, msg.payload.decode())

client.on_connect = on_connect
client.on_message = on_message
client.connect(host, port, 60)
client.loop_forever()
