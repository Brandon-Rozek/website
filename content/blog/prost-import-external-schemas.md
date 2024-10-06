---
title: "Importing External Schemas in Prost"
date: 2024-10-05T11:19:37-07:00
draft: false
tags: []
math: false
medium_enabled: false
---

[Prost](https://github.com/tokio-rs/prost) is a popular Protocol Buffers implementation written in Rust. The `protoc` command is commonly used to generate serializers and de-serializers for many different languages. However, the Prost team instead recommends compiling the Protocol Buffers schema directly within `build.rs`. 

In this post, I'll give a quick tutorial on how I compiled my Protocol Buffers schema when I needed to depend on another package with its own PB messages.

Let's say I have a Rust package called `people`. It contains a file called `Person.proto` with the following contents:

```protobuf
syntax = "proto3";
package people;

message Employee {
  string name = 1;
  string position = 2;
}
```

For sake of our example, we'll assume they exposed the data structures via a `proto` submodule. However, you can check what the module name actually is by looking at the package's codebase for something like

```rust
pub mod namespace_name_goes_here {
    #![allow(missing_docs)]
    include!(concat!(env!("OUT_DIR"), "/people.rs"));
}
```

Now to the package we're creating (which I'll call `company`), First, make sure that you added the `people` package to the Cargo.toml.

Then say that we have the following file `schemas/Team.proto`

```protobuf
syntax = "proto3";
package company;

import "Person.proto"

message Team {
  repeated people.Employee members = 1;
}
```

To compile our new message, we need to tell `build.rs` where it can find both the `Person.proto` and the `Team.proto` schema files, as well as how to reference the messages in the `people` namespace.

```rust
fn main() {
    // Other awesome build stuff
    generate_schemas();
}
fn generate_schemas() {
    let mut config = prost_build::Config::new();
    // Map the people protocol buffer namespace to the people::proto Rust module
    config.extern_path(".people", "people::proto");
    config
        .compile_protos(
            // Files we want to compile
            &["./schema/Team.proto"],
            // Folders where we can find our imports
            &["./schema"],
        )
        .expect("Prost protobuf compilation error;");
}
```

The function `extern_path` takes two arguments, the first one is the name of the namespace within the Protocol Buffers schema, and the second argument is the namespace within Rust.

The first argument of `compile_protos` is the files that we want to compile, the second argument is the directories in which we can find our schemas.

Note that we import `People.proto` in our new Protocol Buffers schema. Currently the only way that I know to get this to work, is to manually copy the `.proto` file in the other package into your own application. 

There you have it! Next you can include the generated output into your Rust application. If you know of a better way to include external schemas without copying the schemas, please reach out. 
