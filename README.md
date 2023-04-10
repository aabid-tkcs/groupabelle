# Groupabelle: Isabelle Formalization of Free Groups and Algorithms on Free Groups

The files here contains the formalisation of various results in the theory of free groups, which are described
in the paper “Formalizing Free Groups in Isabelle/HOL: The Nielsen-Schreier Theorem and the
Conjugacy Problem.
The following files are a part of the formalisation and contain original work by the author(s):
1. Cancellation.thy
2. Conjugacy.thy
3. Conjugacy_Problem.thy
4. Distinct_Inverse.thy
5. FreeGroupMain.thy
6. Freegroup_with_Basis.thy
7. Minimal.thy
8. NielsenScheier.thy
9. N_Properties.thy
10. UniversalProperty.thy
11. Word_Problem.thy


Following file, is a part of an archive of formal proof distribution, has been added only for the purpose of the ease of the review process. It contains a truncated version of the original file. Author(s) do not make any claims of original development with regards to the formalisations contained in the following file. It has been redistributed under the permissions granted by BSD license.
12. Generators.thy
The original file and package is available as the article Generators.thy in: 
                                 https://devel.isa-afp.org/entries/Free-Groups.html

The following files contain the Haskell code extracted from our formalisation, using Isabelle’s code
generation, for the Word Problem and Conjugacy Problem respectively.
1. WP.hs
2. CP.hs

To run all the files in the formalization (along with their dependencies), one could simply run
Nielsen_Schreier.thy
