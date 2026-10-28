import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients

/-! # Cech Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient

noncomputable section

section

/-! The actual coefficient-ring equivalences on the finite tuple
intersections of a family cover land in the original reduced Cech rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)

def dualReducedCechCover (i : I) : X.left.Opens :=
  (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U i

theorem dualReducedCechIntersection {n : ℕ} (a : Fin (n + 1) → I) :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a =
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (dualReducedCechCover X U) a := by
  ext x
  exact (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x)).trans
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection (dualReducedCechCover X U) a x).symm

theorem dualCechIntersection_affine
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (hU : ∀ i, IsAffineOpen (U i)) {n : ℕ} (a : Fin (n + 1) → I) :
    IsAffineOpen (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :=
  IsAffineOpen.iInf (fun i => hU (a i))

def dualCechSectionCoefficientEquiv
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (hU : ∀ i, IsAffineOpen (U i)) {n : ℕ} (a : Fin (n + 1) → I) :
    Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ≃+*
      DualNumber Γ(X.left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (dualReducedCechCover X U) a) :=
  (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (dualCechIntersection_affine X U hU a)).trans
    (NumberRingEquivalence.dualNumberRingEquiv (Regular.SectionTransport.regularSectionTransport (dualReducedCechIntersection X U a)))

end

section

/-! The actual coefficient maps on tuple intersections commute with
all Cech face restrictions, for sections and for units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))

theorem dualCechSectionCoefficientEquiv_precomp {n m : ℕ} (a : Fin (m + 1) → I)
    (σ : Fin (n + 1) → Fin (m + 1))
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ σ))) :
    dualCechSectionCoefficientEquiv X U hU a
      ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ)).op s) =
    NumberCoefficients.dualNumberRingMap (X.left.presheaf.map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (dualReducedCechCover X U) a σ)).op).hom
        (dualCechSectionCoefficientEquiv X U hU (a ∘ σ) s) := by
  change NumberCoefficients.dualNumberRingMap (Regular.SectionTransport.regularSectionTransport (dualReducedCechIntersection X U a)).toRingHom
      (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (dualCechIntersection_affine X U hU a)
        ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
          (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ)).op s)) = _
  rw [DualOpen.SectionRestriction.dualOpenSectionCoefficientEquiv_restrict X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ)
    (dualCechIntersection_affine X U hU (a ∘ σ)) (dualCechIntersection_affine X U hU a) s]
  apply TrivSqZeroExt.ext
  · exact Regular.SectionTransport.regularSectionTransport_restrict (dualReducedCechIntersection X U (a ∘ σ))
      (dualReducedCechIntersection X U a)
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (dualReducedCechCover X U) a σ) _
  · exact Regular.SectionTransport.regularSectionTransport_restrict (dualReducedCechIntersection X U (a ∘ σ))
      (dualReducedCechIntersection X U a)
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (dualReducedCechCover X U) a σ) _

theorem dualCechUnitCoefficient_precomp {n m : ℕ} (a : Fin (m + 1) → I)
    (σ : Fin (n + 1) → Fin (m + 1))
    (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ σ))ˣ) :
    Units.map (dualCechSectionCoefficientEquiv X U hU a).toMonoidHom
      (Units.map ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a σ)).op).hom.toMonoidHom u) =
    UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (dualReducedCechCover X U) a σ)
      (Units.map (dualCechSectionCoefficientEquiv X U hU (a ∘ σ)).toMonoidHom u) := by
  apply Units.ext
  exact dualCechSectionCoefficientEquiv_precomp X U hU a σ u.val

end

section

/-! The actual coefficient map takes restriction from each frame
open to a tuple intersection to the original reduced restriction map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))

theorem dualCechSectionCoefficient_vertex {n : ℕ} (a : Fin (n + 1) → I) (k : Fin (n + 1))
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U (a k))) :
    dualCechSectionCoefficientEquiv X U hU a
      ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k)).op s) =
    NumberCoefficients.dualNumberRingMap (X.left.presheaf.map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a k)).op).hom
        (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (U (a k)) (hU (a k)) s) := by
  change NumberCoefficients.dualNumberRingMap (Regular.SectionTransport.regularSectionTransport (dualReducedCechIntersection X U a)).toRingHom
    (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (dualCechIntersection_affine X U hU a)
      ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k)).op s)) = _
  rw [DualOpen.SectionRestriction.dualOpenSectionCoefficientEquiv_restrict X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k)
    (hU (a k)) (dualCechIntersection_affine X U hU a) s]
  apply TrivSqZeroExt.ext
  · exact Regular.SectionTransport.regularSectionTransport_restrict rfl (dualReducedCechIntersection X U a)
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a k) _
  · exact Regular.SectionTransport.regularSectionTransport_restrict rfl (dualReducedCechIntersection X U a)
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a k) _

theorem dualCechUnitCoefficient_vertex {n : ℕ} (a : Fin (n + 1) → I) (k : Fin (n + 1))
    (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U (a k))ˣ) :
    Units.map (dualCechSectionCoefficientEquiv X U hU a).toMonoidHom
      (Units.map ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k)).op).hom.toMonoidHom u) =
    UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a k)
      (Units.map (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (U (a k)) (hU (a k))).toMonoidHom u) := by
  apply Units.ext
  exact dualCechSectionCoefficient_vertex X U hU a k u.val

end

/-! Normalized infinitesimal gauges lift through the actual affine
coefficient equivalences to regular units on the nonreduced family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))

theorem exists_regular_gauge_of_dual_cech
    (u : ∀ a : Fin 2 → I, Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)ˣ)
    (g : ∀ i, (DualNumber Γ(X.left, dualReducedCechCover X U i))ˣ)
    (hg : ∀ a : Fin 2 → I, Units.map (dualCechSectionCoefficientEquiv X U hU a).toMonoidHom (u a) =
      UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a 1) (g (a 1)) /
      UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (dualReducedCechCover X U) a 0) (g (a 0))) :
    ∃ r : ∀ i, Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U i)ˣ, ∀ a : Fin 2 → I, u a =
      Units.map ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op).hom.toMonoidHom (r (a 1)) /
      Units.map ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op).hom.toMonoidHom (r (a 0)) := by
  let r (i : I) : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U i)ˣ :=
    Units.map (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (U i) (hU i)).symm.toMonoidHom (g i)
  have hr (i : I) : Units.map (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (U i) (hU i)).toMonoidHom (r i) = g i := by
    apply Units.ext
    exact (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (U i) (hU i)).apply_symm_apply (g i).val
  refine ⟨r, fun a => ?_⟩
  apply Units.map_injective (f := (dualCechSectionCoefficientEquiv X U hU a).toMonoidHom)
    (dualCechSectionCoefficientEquiv X U hU a).injective
  rw [map_div, dualCechUnitCoefficient_vertex, dualCechUnitCoefficient_vertex, hr, hr]
  exact hg a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient
