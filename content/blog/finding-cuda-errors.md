---
title: "Finding Cuda Errors"
date: 2022-03-08T10:53:43-05:00
draft: false
tags: []
math: false
---

When cuda fails, it fails silently. To combat this, I have gotten into a habit of checking for a failed status for every cuda memory allocation, kernel execution etc. The following is a C++ macro I wrote that checks if a previous cuda call has failed and then prints the current line and file of the macro.

```c++
#define checkCudaError() { if (cudaGetLastError() != cudaSuccess) { printf("[%s:%d] A previous CUDA call failed.\n", __FILE__, __LINE__); }
```

I recommend using this macro after every cuda call. For example,

```c++
cudaMemcpy(dst, src, size, cudaMemcpyHostToDevice); checkCudaError();
```

During runtime if the call failed, then you will see:

```
[example.cu:14] A previous CUDA call failed.
```

Note that it states whether or not a previous cuda call has failed and not where it has failed at. By putting the macro after every cuda call, you can narrow down which call causes the failure to occur.