# Verkle Tree
A simple verkle tree using MarlinKZG commitment scheme. At each evaluation point, the commitment of each level up until the root will be generated and ultimately batch check all at once. 

## Improvements
- Currently, the 'hash function' is just a basic summation of x and y. Ideally, a correct hash function can be implemented
- Right now, a batch proof is created for each evaluation point. And the verify them, I loop through each one of them and ensure that they are correct. Potentially, it is possible to generate and commitment that includes all the evaluation points without overlap.
- Some possible refactoring can be done especially in the creating of a polynomial commitment