import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeKernelFromChosen
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates

/-! # From Chosen -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FromChosen

noncomputable section

/-! Reconstruct an actual polarized isogeny's entire canonical kernel
from its chosen components. Opposite components are derived through
character descent and Rosati; no complete-kernel comparison is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeKernelFromChosen OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Opposite
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment

variable {k : Type} [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable (ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρA)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian)
variable (hfρ : ∀ a, ρA.map a ≫ f.hom = f.hom ≫ ρB.map a)
variable (n : ℕ)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ (q ^ n) = 1)
variable (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ (q ^ n))
variable (hdegree : q.Coprime (∏ i, ε i))

include hfρ in
omit [IsAlgClosed k] [NumberField.IsCMField E] in
theorem equivariant_kernel_component (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T)) (hx : x.val ≫ f.hom = 1) :
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ T x).val ≫ f.hom = 1 := by
  change (x.val ≫ ρA.map (j.projector iota hsplit n τ)) ≫ f.hom = 1
  rw [Category.assoc, hfρ, ← Category.assoc, hx, MonObj.one_comp]

variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PA ρA (labels (v, false)) n))
variable (hchosen : ∀ (v : Fin s) (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T)),
    x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false))) = x.val →
    (x.val ≫ f.hom = 1 ↔ ∃ h : T ⟶ (H v).group.X,
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit PA ρA n (labels (v, false)) (H v) T h = x))

include hchosen in
omit [IsAlgClosed k] [NumberField.IsCMField E] in
theorem chosen_image_killed (v : Fin s) (T : Over (Spec (.of k))) (h : T ⟶ (H v).group.X) :
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit PA ρA n (labels (v, false)) (H v) T h).val ≫ f.hom = 1 :=
  (hchosen v T _ (congrArg Subtype.val
    (PrescribedKernelOf.Containment.prescribedChosenPoint_component_self j iota hsplit PA ρA n (labels (v, false)) (H v) T h))).mpr ⟨h, rfl⟩

include hρ hfρ hk hpol hdegree hlabels hchosen in
theorem opposite_kernel_iff_chosen_image (v : Fin s) (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hx : x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, true))) = x.val) :
    x.val ≫ f.hom = 1 ↔
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ (H v).group.X),
        AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal PA (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
          (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit PA ρA n (labels (v, false)) (H v) U h)
          ((PA.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  have ho := OppositeKernelFromChosen.opposite_kernel_iff_chosen_orthogonal j iota hsplit PA PB ρA ρB hρ f hfρ n hk hpol hdegree
    (labels (v, false)) (labels (v, true)) (hlabels v) T x hx
  constructor
  · intro hkill U t h
    exact ho.mp hkill U t _ (chosen_image_killed j iota hsplit PA PB ρA f n s labels H hchosen v U h)
      (congrArg Subtype.val (PrescribedKernelOf.Containment.prescribedChosenPoint_component_self j iota hsplit PA ρA n
        (labels (v, false)) (H v) U h))
  · intro htest
    apply ho.mpr
    intro U t y hy hs
    obtain ⟨h, hh⟩ := (hchosen v U y hs).mp hy
    exact hh ▸ htest U t h

include hρ hfρ hk hpol hdegree hlabels hchosen in
theorem full_kernel_of_chosen_criterion (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme) :
    a ≫ f.hom = 1 ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit PA ρA n s labels H T a := by
  have hfixed (τ : Gal(E/ℚ)) (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ T x).val ≫
        ρA.map (j.projector iota hsplit n τ) =
          (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ T x).val :=
    PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit PA.abelian ρA n τ T x.val x.property
  constructor
  · intro ha
    let x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T) := ⟨a, hk T a ha⟩
    refine ⟨x, rfl, fun v => ⟨?_, ?_⟩⟩
    · exact (hchosen v T _ (hfixed (labels (v, false)) x)).mp
        (equivariant_kernel_component j iota hsplit PA PB ρA ρB f hfρ n (labels (v, false)) T x ha)
    · have ho := (opposite_kernel_iff_chosen_image j iota hsplit PA PB ρA ρB hρ f hfρ n hk hpol hdegree
        s labels hlabels H hchosen v T _ (hfixed (labels (v, true)) x)).mp
          (equivariant_kernel_component j iota hsplit PA PB ρA ρB f hfρ n (labels (v, true)) T x ha)
      intro U t h
      rw [← PrescribedBlockCoordinates.prescribedBlockComponent_natural]
      exact ho U t h
  · rintro ⟨x, rfl, hx⟩
    let F := (IsMonHom.monoidHom f.hom T).ker
    have hc (v : Fin s) : (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false)))) ∈ F :=
      (hchosen v T _ (hfixed (labels (v, false)) x)).mpr (hx v).1
    have ho (v : Fin s) : (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, true)))) ∈ F := by
      apply (opposite_kernel_iff_chosen_image j iota hsplit PA PB ρA ρB hρ f hfρ n hk hpol hdegree
        s labels hlabels H hchosen v T _ (hfixed (labels (v, true)) x)).mpr
      intro U t h
      rw [PrescribedBlockCoordinates.prescribedBlockComponent_natural]
      exact (hx v).2 U t h
    have hprod : (∏ v : Fin s, (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false)))) *
        (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, true))))) ∈ F :=
      F.prod_mem (fun v _ => F.mul_mem (hc v) (ho v))
    exact (PrescribedBlockCoordinates.prescribed_components_product j iota hsplit PA ρA n s labels T x) ▸ hprod

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FromChosen
