import OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Free Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCech.CrystallineFreeCech

noncomputable section

/-!
# Free representable chains on the native principal Čech nerve

Each actual intersection contributes its free representable presheaf.
The canonical face maps define a chain complex, and exact sheafification
gives its native sheaf complex. Evaluation identifies each term with the
coproduct indexed by tuples and native arrows into their intersections.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial _root_.AlgebraicTopology

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "PSh" => (OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)ᵒᵖ ⥤ V
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

variable (M : SheafInjectives.CrystallineSheafInjectives.Modules p k)

def coefficients : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring ⥤ PSh :=
  CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q ⋙
    Free.YonedaFunctor.FreeYonedaFunctor.presheaf (Site.Object p k X) V M

def simplicial : SimplicialObject PSh :=
  N ⋙ (FormalCoproduct.eval _ _).obj (coefficients p k X Q M)

def complex : ChainComplex PSh ℕ :=
  (alternatingFaceMapComplex PSh).obj (simplicial p k X Q s M)

def sheafComplex : ChainComplex (Sheaf J V) ℕ :=
  ((presheafToSheaf J V).mapHomologicalComplex (ComplexShape.down ℕ)).obj (complex p k X Q s M)

def evaluationIso (T : Site.Object p k X) (n : ℕ) :
    ((complex p k X Q s M).X n).obj (op T) ≅
      ∐ (fun t : ((N).obj (op ⦋n⦌)).I =>
        ∐ (fun (_ : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q
          (((N).obj (op ⦋n⦌)).obj t)) => M)) :=
  PreservesCoproduct.iso ((CategoryTheory.evaluation _ V).obj (op T))
    (fun t : ((N).obj (op ⦋n⦌)).I =>
      (coefficients p k X Q M).obj (((N).obj (op ⦋n⦌)).obj t))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCech.CrystallineFreeCech
