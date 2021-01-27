# Algebraic Neural Network Library for Coq 8.11.1.

## Algebraic Neural Network Type

### neuron1Type
Fundamental type of algebraic neural networks without activation function
```
I : Type (* input type *)
O : Type (* output and bias type *)
C : Type (* weight type *)
op : O -> O -> O (* assosiative operation *)
action : C -> I -> O (* operator returns output *)
```

Perceptron is defined on `neuron1Type`
```
MP1parameter Idim Odim : Type
  (*
    parameters of perceptron
      Idim : nat : number of input neurons
      Odim : nat : number of output neurons
  *)

MP1 Idim Odim (p:MP1parameter Idim Odim) : I ^ Idim -> O ^ Odim.
  (*
    perceptron as a function
  *)
```

### NNetType
`neuron1Type` with activation function

Multilayer Perceptron is defined on `NNetType`
```
MPparameter Idim l Odim : Type
  (*
    paramters of multilayer perceptron
      Idim : nat : number of input neurons
      Odim : nat : number of output neurons
      l : seq nat : sequence of the numbers of each hidden neurons
  *)

MPfunction Idim l Odim (p:MPparameter Idim l Odim) : I ^ Idim -> O ^ Odim
  (*
    multilayer perceptron as a function
  *)
```

###


## Notice
In "ReLUMPsolvable.v", we generalize an upper and lower bounds of expressive number of single hidden layer ReLU neural networks shown in "Expressive power of neural networks by the number of data that can be expressed".
https://search.ieice.org/bin/index.php?category=D&lang=E&vol=J102-D&num=6&abst=j
This paper is written in Japanese, but the definition of expressive number and these theoriese in English are written in "Expressive Number of Two or More Hidden Layer ReLU Neural Networks".
https://ieeexplore.ieee.org/document/8951658
or
https://www.jstage.jst.go.jp/article/ijnc/10/2/10_293/_article/-char/en/

All code are written by Kenta Inoue.
