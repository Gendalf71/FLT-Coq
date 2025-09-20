# FLT-Coq 
## Check FLT proof

The Coq code is correct; it provides a formalization of FLT that compiles successfully.

## Fermat's Theorem – Fermat's Own Proof (c) Yurkin Pavel IAEA

Russian nuclear physicist Grigory Leonidovich Dedenko has reconstructed the original reasoning of Pierre de Fermat, which led him to conclude that the sum of two equal natural powers of rational numbers cannot be represented as the same power for an exponent greater than two — the famous (Great) Fermat's Theorem.

As is known, in 1637 Fermat left a note in the margin of Diophantus's "Arithmetica" (which he was apparently reading) stating the discovered fact and adding: "I have discovered a truly marvelous proof of this, which this margin is too narrow to contain."

According to G.L. Dedenko, Fermat analyzed differences of powers using a then-new method — decomposing these differences into a sum of pairwise products (later named the "Newton binomial"). Fermat found that the coefficients of the decomposition then satisfy certain simple conditions, which are equivalent to a simple logarithmic equation (another concept only maturing by the mid-17th century) with respect to the degree of the decomposed sum (or, more precisely, difference). This equation has only two roots — the numbers one and two.

Thus, the margins of the book indeed turned out to be too narrow for a full recording of the marvelous proof — it needed to be preceded and interleaved with the introduction and lemmas of new concepts at that time: decomposition with combinatorial coefficients (Newton's binomial), logarithm, etc. It is now unclear whether Pierre de Fermat ever wrote out his reasoning in detail anywhere, and if he did, whether that record now lies in some unexpected archive. Historians of science are invited to search again.

The fully working Coq code is attached, as is the PDF of the reconstructed proof of Fermat's Theorem.

