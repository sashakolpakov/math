import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.MappedLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CommutativeGroupLawEquations

/-! # Base Change Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! For every scheme base change, the actual transported operations satisfy the commutative-group laws exactly on the six pulled-back equation loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {X : Over S} (D : Operations.FamilyGroupOperations X)

def Operations.FamilyGroupOperations.baseChange (f : T ⟶ S) : Operations.FamilyGroupOperations ((Over.pullback f).obj X) :=
  D.map (Over.pullback f)

theorem Operations.FamilyGroupOperations.mappedLaws_iff_equations [IsProper X.hom] [Flat X.hom]
    (F : Over S ⥤ Over T) [F.Monoidal] :
    D.MappedLaws F ↔ ∀ e ∈ D.equations, F.map e.lhs = F.map e.rhs := by
  simp only [Operations.FamilyGroupOperations.equations, List.forall_mem_cons]
  exact ⟨fun h => ⟨h.one_mul, h.mul_one, h.mul_assoc, h.left_inv, h.right_inv, h.mul_comm,
      fun e he => (List.not_mem_nil he).elim⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩

theorem Operations.FamilyGroupOperations.baseChange_laws_iff [IsProper X.hom] [Flat X.hom] (f : T ⟶ S) :
    (D.baseChange f).Laws ↔
      ∀ e ∈ D.equations, (Over.pullback f).map e.lhs = (Over.pullback f).map e.rhs :=
  (D.map_laws_iff (Over.pullback f)).trans (D.mappedLaws_iff_equations (Over.pullback f))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
