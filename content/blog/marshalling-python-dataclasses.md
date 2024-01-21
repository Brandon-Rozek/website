---
title: "Marshalling Python Dataclasses"
date: 2024-01-20T22:52:50-05:00
draft: false 
tags:
    - Python
math: false
medium_enabled: false
---

Recently I wanted a way to transfer structured messages between two python applications over a unix domain socket. The cleanest and simplest way I found so far is to make use of the dataclasses and json standard libraries.

We'll consider the following message for the rest of the post:

```python
from dataclasses import dataclass

@dataclass
class QueryUserMessage:
    auth_key: str
    username: str
```

## Marshalling

Let's say we have a message we want to send:

```python
message = QueryUserMessage("lkajdfsas", "brozek")
```

We first need to get its dictionary representation. Luckily the standard library has us there:

```python
from dataclasses import asdict

message_dict = asdict(message)
```

Then we can use the `json` module to give us a string representation

```python
import json

message_str = json.dumps(message_dict)
```

Finally, we can encode it into bytes and send it away:

```python
# Default encoding is "utf-8"
message_bytes = message_str.encode()
# Assuming connetion is defined...
connection.sendall(message_bytes)
```

To make this easier for myself, I create a custom `json` encoder and a function that uses the connection to send off the message

```python
class DataclassEncoder(json.JSONEncoder):
    def default(self, o):
        return asdict(o)
def send_message(connection, message_dataclass):
    contents = json.dumps(message_dataclass, cls=DataclassEncoder).encode()
    connection.sendall(contents)
```

## Un-marshalling

On the other end, let us receive the bytes and decode it into a string:

```python
MESSAGE_BUFFER_LEN = 1024
message_bytes = connection.recv(MESSAGE_BUFFER_LEN)
message_str = message_bytes.decode()
```

We can use the `json` module to turn it into a Python dictionary

```python
message_dict = json.loads(message_str)
```

In this post, we can make use of the fact that we only have one message class. In other cases, you would either want to rely on some protocol or pass in the message type ahead of time. Therefore, we can pass the fields of the dictionary straight to the constructor.

```python
message = QueryUserMessage(**message_dict)
```

## Conclusion

In production use cases, we'll need to introduce a gambit of error-handling to capture failures in json de-serialization and class instantiation. I hope, however, that this serves as a good starting point. 

Some things to consider:

1) If you have multiple types of messages, maybe including a field in the dictionary that is a string which represents the message type. Both applications can then maintain a map between these strings and the class constructors.
2) If it's possible to have messages larger than the buffer length, then consider either setting it higher or sending the size of the message beforehand.
3) Using a standard HTTP library ;)
