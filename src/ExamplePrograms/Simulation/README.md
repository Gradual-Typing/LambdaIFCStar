To create a new simulation test case:

1. create an Agda module named `YourExample.agda`
2. write two $\lambda_{\mathtt{SEC}}^\star$ programs and their
   typing derivations
3. add two lines to `Examples.agda`:
  1. `open import ExamplePrograms.Simulation.YourExample as Example`
  2. `cfgs = ... ⟨ "Values" , Values.M , Values.M′ , _ , _ , Values.⊢M , Values.⊢M′ ⟩ ∷ ...`,
     where the first string is the name of the test case
