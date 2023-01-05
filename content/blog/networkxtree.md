---
title: "Tree-based Plots in NetworkX"
date: 2022-01-02T20:36:41-05:00
draft: false
tags: ["Python"]
math: false
medium_enabled: true
---

A graph in D3 and NetworkX can be represented as a JSON file.

Example:

```json
{
    "nodes": [
        {"id": 1, "name": "A"},
        {"id": 2, "name": "B"},
        {"id": 3, "name": "C"}
    ],
    "links": [
        {"source": 1,"target": 2},
        {"source": 1,"target": 3}
    ]
}
```

The `nodes` entry in the JSON is a list containing a `node` object. Each `node` object has a unique id and a name which can appear inside the node in the drawing.

The `links` entry in the JSON is a list of `link` objects which each denote a (directed) edge between a source and target id.

To run the following script you'll need `graphwiz` installed on the system. You'll also need to have the python packages `networkx` and `pydot`.

```python
import networkx as nx
from networkx.readwrite import json_graph
from networkx.drawing.nx_pydot import graphviz_layout
import matplotlib.pyplot as plt

# Replace graph_json variable with JSON representation of graph
graph_json = {"nodes": [{"id": 1, "name": "A"},{"id": 2, "name": "B"}],"links": [{"source":1,"target":2}]}

node_labels = {node['id']:node['name'] for node in graph_json['nodes']}
for n in graph_json['nodes']:
    del n['name']
g = json_graph.node_link_graph(graph_json, directed=True, multigraph=False)
pos = graphviz_layout(g, prog="dot")
nx.draw(g.to_directed(), pos, labels=node_labels, with_labels=True)
plt.show()
```

Given the JSON from the top of the post it'll produce:

![image-20220103000837137](/files/images/blog/20220103000837137.png)
