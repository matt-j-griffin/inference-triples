# Abstract Inference Triples for Isabelle/HOL

Many theories in Isabelle/HOL’s core and the Archive of Formal Proofs (AFP) contain formulations 
based on Hoare logic and Incorrectness logic. 
These often duplicate the well-established syntax and rules of Hoare and O’Hearn-style triples. 

This formalisation aims to provide logic-agnostic, abstract encodings of Hoare and O’Hearn 
triples using classes, enabling both current and future developments of Hoare and Incorrectness 
logic to share a common foundation. 
