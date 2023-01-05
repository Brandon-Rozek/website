---
date: 2022-11-12 21:27:42-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: ddffc5b14ef9
tags:
- Functional Programming
- Scala
title: Immutable Traversals with Unfold
---

Let's consider the following binary tree:

```goat
                   a                                                                       
                  / \                          
                 /   \         
                b     d                    
                 \        
                  \       
                   c       
```





We can encode this with the following Scala code:

```scala
final case class BinNode(
    val label: String,
    val left: Option[BinNode],
    val right: Option[BinNode]
)

// Leaf Nodes
val c_node = BinNode("c", None, None)
val d_node = BinNode("d", None, None)
// Rest of nodes
val b_node = BinNode("b", None, Some(c_node))
val a_node = BinNode("a", Some(b_node), Some(d_node))
```

For depth first search, an intuitive immutable implementation would be a recursive function.

```scala
// Using Preorder traversal
def DFS(node: BinNode): Iterator[BinNode] = 
    lazy val left_side = node.left.fold(Iterator.empty[BinNode])(DFS)
    lazy val right_side = node.right.fold(Iterator.empty[BinNode])(DFS)
    Iterator(node) ++ left_side ++ right_side
```

Let's evaluate this using our example above:

```scala
DFS(a_node).toList.map(_.label)
// List(a, b, c, d)
```

The recursive implementation inherently uses the system stack to keep track of the nodes.  This means that the last element gets evaluated in each step. Otherwise called last-in-first-out (LIFO). Breadth first search, however, uses a queue based approach where the first one added to the data structure is the first one considered (FIFO). 

To preserve immutability in our code, we can use `unfold`. Here our state is the queue of nodes.

```scala
def BFS(node: BinNode): Iterator[BinNode] =
    Iterator.unfold(List(node))(q =>
        if q.isEmpty then
            None
        else
            val crnt_node = q.head
            val next_q = q.tail ++ crnt_node.left ++ crnt_node.right
            Some(crnt_node, next_q)
    )
```

Evaluating on our example:

```scala
BFS(a_node).toList.map(_.label)
// List(a, b, d, c)
```

We can also use `unfold` for the depth first search approach as well. We can replace the list used with a stack.

```scala
import scala.collection.mutable.Stack
def DFS2(node: BinNode): Iterator[BinNode] = 
    Iterator.unfold(Stack(node))(s =>
        if s.isEmpty then
            None
        else
            val crnt_node = s.pop()
            s.pushAll(crnt_node.right)
            s.pushAll(crnt_node.left)
            Some(crnt_node, s)
    )
```

Using a stack introduces some mutability. We can use the immutable list data structure instead, as long as we satisfy the LIFO ordering.

```scala
def DFS3(node: BinNode): Iterator[BinNode] = 
    Iterator.unfold(List(node))(s =>
        if s.isEmpty then
            None
        else
            val crnt_node = s.last
            val next_s = s.init ++ crnt_node.right ++ crnt_node.left
            Some(crnt_node, next_s)
    )
```