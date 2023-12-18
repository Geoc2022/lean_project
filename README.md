# Final Project (Surreal Numbers) 

Here is some work with trying to create the surreal numbers in lean. The [axiom_based.lean](axiom_based.lean) file works through a bit of the story of the surreal numbers from Knuth's [book](https://people.math.harvard.edu/~knill/teaching/mathe320_2015_fall/blog15/surreal1.pdf). One of the main problems with dealing with the surreal numbers is that the numbers contain other numbers in Sets, causing ordering to be difficult. The axiom based approach is a way to get around this problem. However, it's not that elegant. Another approach is to "trick" lean and use lists which can be changed to sets later in [axiom_based.lean](axiom_based.lean). This approach is more elegant, but it's still difficult to prove theorems about the surreal numbers.

Nimbers are a subset of the surreal numbers (ex. * = {0|0}). I made a little playground for nimbers in [nim.lean](nim.lean). 

While playing around I found these sources interesting:
- https://sites.math.rutgers.edu/~zeilberg/EM13/onag1.pdf (animated: https://www.youtube.com/watch?v=ZYj4NkeGPdM)
- https://people.math.harvard.edu/~knill/teaching/mathe320_2015_fall/blog15/surreal1.pdf
- https://arxiv.org/pdf/math/0410026v2.pdf
- https://www.whitman.edu/documents/Academics/Mathematics/Grimm.pdf

