import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism
import Mathlib.Data.Fin.Tuple.Basic

/-! # Enhancement Extension -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! A CM enhancement may retain additional specified endomorphisms without losing rigidity. -/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

def AlgebraicEnhancement.Abelian.CMEnhancement.append {A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (E : AlgebraicEnhancement.Abelian.CMEnhancement A)
    {r : ℕ} (m : Fin r → (A.toOver ⟶ A.toOver)) (hm : ∀ i, IsMonHom (m i)) :
    AlgebraicEnhancement.Abelian.CMEnhancement A where
  size := E.size + r
  map := Fin.addCases E.map m
  group i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using E.group j
    · intro j
      simpa only [Fin.addCases_right] using hm j
  rigid W hW hInv := by
    apply E.rigid W hW
    intro i x hx
    simpa only [Fin.addCases_left] using hInv (Fin.castAdd r i) x hx

def AbelianEndomorphism.AbelianEndomorphismTuple.append
    {g r n : ℕ} {S : AlgebraicGeometry.Scheme} {A : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin r) A) (b : AbelianEndomorphism.AbelianEndomorphismTuple (Fin n) A) :
    AbelianEndomorphism.AbelianEndomorphismTuple (Fin (r + n)) A where
  map := Fin.addCases a.map b.map
  group i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using a.group j
    · intro j
      simpa only [Fin.addCases_right] using b.group j

end

end OAI.ArithmeticGeometry.Descent.CMVariety
