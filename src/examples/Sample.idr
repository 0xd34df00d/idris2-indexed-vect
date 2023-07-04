import Data.Vect.Indexed

SampleVect : IVect 5 (\idx => (n ** n = idx))
SampleVect = [ (0 ** Refl), (1 ** Refl), (2 ** Refl), (3 ** Refl), (4 ** Refl) ]

TabulatedVect : IVect 5 (\idx => (n ** n = idx))
TabulatedVect = tabulate (\idx => (idx ** Refl))

theyAreEqual : SampleVect = TabulatedVect
theyAreEqual = Refl
