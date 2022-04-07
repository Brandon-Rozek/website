---
title: "Networkx Random Sample Graph"
date: 2022-04-07T19:48:12-04:00
draft: false
tags: []
math: false
---

I've been working on several algorithms in `networkx`. In order to speed up testing, especially on large graphs, I've been randomly sampling portions of the original graph. The best way I've found to do this is through the following python snippet:

```python
import random
random_sample_edges = random.sample(list(G.edges), SAMPLE_SIZE)
G_sample = nx.Graph()
G_sample.add_edges_from(random_sample_edges)
```

It might be tempting to sample the nodes and then grab the subgraph like the following:

```python
import random
random_nodes = random.sample(list(G.nodes), SAMPLE_SIZE)
G_sample = G.subgraph(random_nodes)
```

However, only considering the nodes when sampling  makes it highly likely that the subgraph will significantly less edges. This results in a mostly disconnected subgraph and a loss of information. Sampling the edges prevents this issue at the expense of not capturing single nodes not connected to anything else. 
