# Generalized cryptanalysis of RSA with small public exponent

## Introduction

This is a Python implementation of lattice-based attack proposed in **Generalized cryptanalysis of RSA with small public exponent**[^GRSA]. The so-called *Algebraic Independence Assumption* seems to be untenable in the simulated attacks. I still try to implement such attack to show the basic idea and illustrate it with toy examples.

## Requirements

- [**SageMath**](https://www.sagemath.org/) 9.5 with Python 3.10

You can check your SageMath Python version using the following command:

```commandline
$ sage -python --version
Python 3.10.12
```

Note: If your SageMath Python version is older than 3.9.0, some features in given scripts might not work.

## Usage

The standard way to run the attack with given parameters $N$, $e$, $\beta$, $\gamma$ and $s$ requires passing them as arguments step by step in command line. For instance, to run the attack with given parameters used in our paper, please first run `sage -python attack.py` and then type known parameters as indicated (toy examples with $16$-bit primes):

```commandline
GRSA$ sage -python attack.py
Input given parameters of GRSA attack instance as follows
Input N: 1441516961
Input e: 55331
Input b: 0.65
Input g: 0.5
Input s: 6
Equation: y*z + 55331*x + 13631866/17*y - 1 = 0
Found primes: p = 40231, q = 35831
The attack costs 1.800 seconds...
```

```commandline
GRSA$ sage -python attack.py
Input given parameters of GRSA attack instance as follows
Input N: 1229575093
Input e: 39979
Input b: 0.63
Input g: 0.22
Input s: 6
Equation: y*z + 39979*x + 1271812/13*y - 1 = 0
Found primes: p = 35983, q = 34171
The attack costs 3.745 seconds...
```

## Notes

All the details of the numerical attack experiments are recorded in the `attack.log` file. A more efficient lattice reduction algorithm [flatter](https://github.com/keeganryan/flatter) is used and `USE_FLATTER = True`.

[^GRSA]: Zheng M., Hu H., Wang Z., "Generalized cryptanalysis of RSA with small public exponent" | [PDF](https://mengcezheng.github.io/docs/ZHW16.pdf)
