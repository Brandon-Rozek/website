---
date: 2022-12-01 21:12:03-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 80a6f9baadf4
tags:
- Python
title: 'Quick Python: Check Submodule Load'
---

Reading other people's code is a great way to learn. Recently, I was looking at the `numpy` repository and they had a hidden gem within their `setup.py`. In large scale repositories like `numpy`, we can have different dependencies that we rely upon via *git submodules*. The following function will check to see that these dependencies are loaded and in a "clean" state.

```python
def check_submodules():
    """ verify that the submodules are checked out and clean
        use `git submodule update --init`; on failure
    """
    if not os.path.exists('.git'):
        return
    with open('.gitmodules') as f:
        for line in f:
            if 'path' in line:
                p = line.split('=')[-1].strip()
                if not os.path.exists(p):
                    raise ValueError('Submodule {} missing'.format(p))

    proc = subprocess.Popen(['git', 'submodule', 'status'],
                            stdout=subprocess.PIPE)
    status, _ = proc.communicate()
    status = status.decode("ascii", "replace")
    for line in status.splitlines():
        if line.startswith('-') or line.startswith('+'):
            raise ValueError('Submodule not clean: {}'.format(line))
```

To get a better idea of what this piece of code is doing, let's trace through its execution. The `.gitmodules` file defines where each of the submodules are stored in the repository. Here's the file for `numpy`'s repository.

```ini
[submodule "doc/source/_static/scipy-mathjax"]
	path = doc/source/_static/scipy-mathjax
	url = https://github.com/scipy/scipy-mathjax.git
[submodule "numpy/core/src/umath/svml"]
	path = numpy/core/src/umath/svml
	url = https://github.com/numpy/SVML.git
```

The function then checks if each of the `path` locations are defined in the filesystem.

```python
# Check #1
if not os.path.exists("doc/source/_static/scipy-mathjax"):
    raise ValueError('Submodule {} missing'.format("doc/source/_static/scipy-mathjax"))

# Check #2
if not os.path.exists("numpy/core/src/umath/svml"):
    raise ValueError('Submodule {} missing'.format("numpy/core/src/umath/svml"))
```

Now it is possible for these submodules to be checked out, but be in some sort of unclean state. For example let's say that I edit `numpy/core/src/umath/svml/README.md` and commit that change. Then the `git submodule status` command will look like the following.

```bash
$ git submodule status
36f4c898f2255e0c98eb6949cd67381552d5ffea ../doc/source/_static/scipy-mathjax (heads/master)
+1f2b5b3cae704ffa6210a638dfd084946da366bf core/src/umath/svml (heads/main-1-g1f2b5b3)
```

Notice the `+` behind the second submodule. According to the man page for `git submodule`

>  Show the status of the submodules. This will print the SHA-1 of the currently checked out commit for each submodule, along with the submodule path and the output of git describe for the SHA-1.
>  
>  Each SHA-1 will possibly be prefixed with
>  -  **-** if the submodule is not initialized
>  - **+** if the currently checked out submodule commit does not match the SHA-1 found in the index of the containing repository 
>  - U if the submodule has merge conflicts.

The existence of the `+` would make this check fail. However, no prefixes will make the check succeed.

By executing this function within the repositories `setup.py`, it verifies that the needed dependencies are checked out and clean before installing the python package. Checks like these make python packages feel a little more stable.