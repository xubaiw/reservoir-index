# Lean
> **Be sure `Nat_` as the type and not `Nat`**

It seems unnecessary to use a package manager like lake, but it was the only way
I could get the imports to work properly. The package name is "Arithmetic" so 
there is the `Arithmetic.lean` file in the base directory and then all other 
files should go in the "Arithmetic" folder and be imported with 
`import Arithmetic.<module>`. The command `lake build` builds the package.