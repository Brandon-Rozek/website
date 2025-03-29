---
title: "Setting up Ollama with CUDA on Podman Quadlets"
date: 2025-03-29T09:59:55-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

[Open WebUI](https://www.openwebui.com/) provides a nice chat interface for interacting with LLMs over Ollama and OpenAI compatible APIs. Using [Ollama](https://ollama.com/), we can self-host many different LLMs that are open-sourced! This post documents the steps that I took in order to get Ollama working with CUDA using my Podman setup. However given how fast Machine Learning projects iterate, I wouldn't be surprised if these exact steps no longer work.  In that case, I'll provide links to the official documentation which hopefully can help.

I'll assume that you have the NVIDIA driver installed on your machine. The steps vary by OS/distribution and how modern of a driver you want, but I generally recommend to stick with what's packaged in your distribution's repository. This is to minimize headaches...

With that, our first step is to install the `nvidia-container-toolkit`.  This package contains a collection of libraries and scripts to help us run our GPU inside a container.

```bash
sudo dnf install nvidia-container-toolkit
```

As of this time of writing, instructions for installing the toolkit can be found on [NVIDIA's website](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/install-guide.html).

We can use this toolkit to generate a Common Device Interface (CDI) file which Podman will use to talk to the GPU.

```bash
sudo nvidia-ctk cdi generate --output=/etc/cdi/nvidia.yaml
```

**Note:** Every time you update your NVIDIA driver, you'll have to run this command.

NVIDIA also documents the steps for configuring CDI on [their website](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/cdi-support.html#running-a-workload-with-cdi). 

From here, we should make sure that the NVIDIA toolkit found the appropriate GPU(s) and has set up their CDI.

```bash
nvidia-ctk cdi list
```

I only have one GPU on my machine, so it outputs something like the following:

```
INFO[0000] Found 3 CDI devices                          
nvidia.com/gpu=0
nvidia.com/gpu=GPU-52785a8a-f8ca-99b9-0312-01a1f59e789b
nvidia.com/gpu=all
```

If you want your container to be able to access all the GPUs, we can use the `nvidia.com/gpu=all` device interface. Otherwise, we can use a specific one.

Then, we restart Podman so that the CDI files are loaded.

```bash
sudo systemctl restart podman
```

For our first test, we'll make sure that the container can appropriately access the GPU by running the `nvidia-smi` command.

```bash
sudo podman run --rm \
	--device nvidia.com/gpu=all \
	docker.io/nvidia/cuda:11.0.3-base-ubuntu20.04 \
	nvidia-smi
```

For my GPU it outputs:

```
+-----------------------------------------------------------------------------------------+
| NVIDIA-SMI 570.124.04             Driver Version: 570.124.04     CUDA Version: 12.8     |
|-----------------------------------------+------------------------+----------------------+
| GPU  Name                 Persistence-M | Bus-Id          Disp.A | Volatile Uncorr. ECC |
| Fan  Temp   Perf          Pwr:Usage/Cap |           Memory-Usage | GPU-Util  Compute M. |
|                                         |                        |               MIG M. |
|=========================================+========================+======================|
|   0  NVIDIA GeForce RTX 3060        Off |   00000000:02:00.0  On |                  N/A |
|  0%   50C    P8             19W /  170W |    1546MiB /  12288MiB |      0%      Default |
|                                         |                        |                  N/A |
+-----------------------------------------+------------------------+----------------------+
                                                                                         
+-----------------------------------------------------------------------------------------+
| Processes:                                                                              |
|  GPU   GI   CI              PID   Type   Process name                        GPU Memory |
|        ID   ID                                                               Usage      |
|=========================================================================================|
+-----------------------------------------------------------------------------------------+

```

Now we are ready to set up Ollama! To save time when running our `systemd` commands, let's pull the image ahead of time.

```bash
sudo podman pull docker.io/ollama/ollama
```

We'll have to save the models somewhere, so in this example we'll save them to `/opt/ollama`.

```bash
sudo mkdir /opt/ollama
```

Let's configure the Quadlet. Save the following to `/etc/containers/systemd/ollama.container`:

```ini
[Container]
ContainerName=ollama
HostName=ollama
Image=docker.io/ollama/ollama
AutoUpdate=registry
Volume=/opt/ollama:/root/.ollama
PublishPort=11434:11434
AddDevice=nvidia.com/gpu=all

[Unit]

[Service]
Restart=always

[Install]
WantedBy=default.target
```

This file specifies the flags that we pass to the podman command:

- Publish the port 11434: This is the port we'll use when sending messages to Ollama from Open WebUI. Of course you're welcome to use other networking tricks to pull that off.
- Mount the folder `/opt/ollama` on the filesystem to `/root/.ollama` within the container: We don't want to have to re-download the LLM models each time! 

For the moment of truth, let's start it!

```bash
sudo systemctl start ollama
```

I won't show in this post how to configure Open WebUI, but we can make sure that everything is working by looking at the Ollama container itself.

```bash
sudo podman exec -it ollama /bin/bash
```

We'll perform a test with a smaller model (1.2 GB):

```bash
ollama run llama3.2:1b
```

Depending on your Internet connection, this will take a couple minutes to download and load onto the GPU.

When it's done the prompt will be replaced with:

```
>>> 
```

From here you can chat with the LLM!

