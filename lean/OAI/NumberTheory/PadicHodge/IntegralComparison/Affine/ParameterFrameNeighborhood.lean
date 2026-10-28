import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Parameter Frame Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterFrameNeighborhood

noncomputable section

/-! A principal ambient neighborhood makes prescribed normal and
quotient parameters an actual differential basis, preserving the entire
closed affine chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (U : Y.left.Opens) (hU : IsAffineOpen U) {c g : ℕ}
  (s : Fin c → f.left.ker.ideal ⟨U,hU⟩) (t : Fin g → Intrinsic.SmoothClosedSections.ring R Y U)
  (b : Module.Basis (Fin (c+g)) (Intrinsic.SmoothClosedSections.ring R Y U) Ω[Intrinsic.SmoothClosedSections.ring R Y U⁄R])

local instance baseAlgebra (V : Y.left.Opens) : Algebra R Γ(Y.left, V) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y V

abbrev determinant : Intrinsic.SmoothClosedSections.ring R Y U :=
  DifferentialBasisNeighborhood.determinant b (Fin.append (fun i => (s i).val) t)

abbrev openSubset : Y.left.Opens := Y.left.basicOpen (determinant R X Y f U hU s t b)

omit [IsClosedImmersion f.left] in
theorem affine : IsAffineOpen (openSubset R X Y f U hU s t b) :=
  hU.basicOpen _

omit [IsClosedImmersion f.left] in
theorem below : openSubset R X Y f U hU s t b ≤ U := Y.left.basicOpen_le _

def normal : Fin c → Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b) :=
  IdealSheafPrincipalEquations.sequence U (determinant R X Y f U hU s t b)
    (fun i => (s i).val)

def parameter : Fin g → Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b) :=
  IdealSheafPrincipalEquations.sequence U (determinant R X Y f U hU s t b) t

def basis : Module.Basis (Fin (c+g)) (Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b))
    Ω[Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b)⁄R] := by
  letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R Y
    (homOfLE (below R X Y f U hU s t b))
  letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R Y
    (homOfLE (below R X Y f U hU s t b))
  letI : IsLocalization.Away (determinant R X Y f U hU s t b)
      (Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b)) := hU.isLocalization_basicOpen _
  exact DifferentialBasisLocalization.Neighborhood.basisAt b (Fin.append (fun i => (s i).val) t)
    (Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b))

omit [IsClosedImmersion f.left] in
theorem basis_eq :
    (basis R X Y f U hU s t b : Fin (c+g) →
      Ω[Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b)⁄R]) =
    Fin.append
      (fun i => KaehlerDifferential.D R _ (normal R X Y f U hU s t b i))
      (fun i => KaehlerDifferential.D R _ (parameter R X Y f U hU s t b i)) := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R Y
    (homOfLE (below R X Y f U hU s t b))
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R Y
    (homOfLE (below R X Y f U hU s t b))
  let : IsLocalization.Away (determinant R X Y f U hU s t b)
      (Intrinsic.SmoothClosedSections.ring R Y (openSubset R X Y f U hU s t b)) := hU.isLocalization_basicOpen _
  funext i
  rw [basis, DifferentialBasisLocalization.Neighborhood.basisAt_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right, normal, parameter,
      IdealSheafPrincipalEquations.sequence] <;> rfl

variable [Smooth X.hom] [Smooth Y.hom]
  (bI : Module.Basis (Fin c) (Intrinsic.SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U,hU⟩)
    (f.left.ker.ideal ⟨U,hU⟩).Cotangent)
  (hI : ∀ i, bI i = (f.left.ker.ideal ⟨U,hU⟩).toCotangent (s i))
  (bQ : Module.Basis (Fin g) (Intrinsic.SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U,hU⟩)
    Ω[Intrinsic.SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U,hU⟩⁄R])
  (hQ : ∀ i, bQ i = KaehlerDifferential.D R (Intrinsic.SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U,hU⟩)
    (Ideal.Quotient.mk _ (t i)))

include hI hQ in
theorem determinant_isUnit : IsUnit
    (Ideal.Quotient.mk (f.left.ker.ideal ⟨U,hU⟩) (determinant R X Y f U hU s t b)) := by
  let : Algebra.Smooth R Γ(Y.left,U) := Intrinsic.SmoothClosedSections.smooth_sections R Y U hU
  let : Algebra.Smooth R (Γ(Y.left,U) ⧸ f.left.ker.ideal ⟨U,hU⟩) :=
    Intrinsic.SmoothClosedSections.smooth_quotient R X Y f U hU
  have hd : (fun i => KaehlerDifferential.D R (Intrinsic.SmoothClosedSections.ring R Y U)
      (Fin.append (fun j => (s j).val) t i)) =
      Fin.append (fun i => KaehlerDifferential.D R (Intrinsic.SmoothClosedSections.ring R Y U) (s i).val)
        (fun i => KaehlerDifferential.D R (Intrinsic.SmoothClosedSections.ring R Y U) (t i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  unfold determinant DifferentialBasisNeighborhood.determinant
  rw [hd]
  exact IntegralComparison.Quotient.ParameterBasis.determinant_isUnit (f.left.ker.ideal ⟨U,hU⟩)
    bI s hI bQ t hQ b

include hI hQ in
theorem preimage : f.left ⁻¹ᵁ openSubset R X Y f U hU s t b = f.left ⁻¹ᵁ U := by
  have hu := (determinant_isUnit R X Y f U hU s t b bI hI bQ hQ).map
    (Intrinsic.SmoothClosedSections.quotientEquiv R X Y f U hU).toRingHom
  change IsUnit (f.left.app U (determinant R X Y f U hU s t b)) at hu
  exact (Scheme.preimage_basicOpen f.left _).trans (X.left.basicOpen_of_isUnit hu)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterFrameNeighborhood
