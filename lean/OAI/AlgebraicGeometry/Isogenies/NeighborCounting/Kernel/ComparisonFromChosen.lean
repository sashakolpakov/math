import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FromChosen

/-! # Comparison From Chosen -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ComparisonFromChosen

noncomputable section

/-! Two actual polarized isogenies with the same chosen kernel
components have the same complete kernel. Their opposite components
are compared by the canonical pairing, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FromChosen OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeKernelFromChosen
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates

variable {k : Type} [Field k] [IsAlgClosed k] {d e r N M L : ℕ}
variable {δ : Fin d → ℕ} {ε : Fin e → ℕ} {ζ : Fin r → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel e ε M (Spec (.of k)))
variable (PC : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel r ζ L (Spec (.of k)))
variable (ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
variable (ρC : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PC.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρA)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian)
variable (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PC.abelian)
variable (hfρ : ∀ a, ρA.map a ≫ f.hom = f.hom ≫ ρB.map a)
variable (hgρ : ∀ a, ρA.map a ≫ g.hom = g.hom ≫ ρC.map a)
variable (n : ℕ)
variable (hfbound : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ (q ^ n) = 1)
variable (hgbound : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ g.hom = 1 → a ^ (q ^ n) = 1)
variable (hfpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ (q ^ n))
variable (hgpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom g.hom PA.dual PC.dual PC.polarization = PA.polarization.isogeny.hom ^ (q ^ n))
variable (hfdegree : q.Coprime (∏ i, ε i)) (hgdegree : q.Coprime (∏ i, ζ i))
variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (hchosen : ∀ (v : Fin s) (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T)),
    x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false))) = x.val →
      (x.val ≫ f.hom = 1 ↔ x.val ≫ g.hom = 1))

include hρ hfρ hgρ hfbound hgbound hfpol hgpol hfdegree hgdegree hlabels hchosen in
theorem full_kernel_imp_from_chosen (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme)
    (ha : a ≫ f.hom = 1) : a ≫ g.hom = 1 := by
  let x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T) := ⟨a, hfbound T a ha⟩
  have hfixed (τ : Gal(E/ℚ)) :
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ T x).val ≫
        ρA.map (j.projector iota hsplit n τ) =
          (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ T x).val :=
    PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit PA.abelian ρA n τ T x.val x.property
  let F := (IsMonHom.monoidHom g.hom T).ker
  have hchosenG (v : Fin s) :
      (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false)))) ∈ F :=
    (hchosen v T _ (hfixed (labels (v, false)))).mp
      (FromChosen.equivariant_kernel_component j iota hsplit PA PB ρA ρB f hfρ n (labels (v, false)) T x ha)
  have hoppositeG (v : Fin s) :
      (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, true)))) ∈ F := by
    let y := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n (labels (v, true)) T x
    have hf := (OppositeKernelFromChosen.opposite_kernel_iff_chosen_orthogonal j iota hsplit PA PB ρA ρB hρ f hfρ n hfbound hfpol hfdegree
      (labels (v, false)) (labels (v, true)) (hlabels v) T y (hfixed (labels (v, true)))).mp
        (FromChosen.equivariant_kernel_component j iota hsplit PA PB ρA ρB f hfρ n (labels (v, true)) T x ha)
    apply (OppositeKernelFromChosen.opposite_kernel_iff_chosen_orthogonal j iota hsplit PA PC ρA ρC hρ g hgρ n hgbound hgpol hgdegree
      (labels (v, false)) (labels (v, true)) (hlabels v) T y (hfixed (labels (v, true)))).mpr
    intro U t z hz hs
    exact hf U t z ((hchosen v U z hs).mpr hz) hs
  have hp : (∏ v : Fin s, (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, false)))) *
      (x.val ≫ ρA.map (j.projector iota hsplit n (labels (v, true))))) ∈ F :=
    F.prod_mem (fun v _ => F.mul_mem (hchosenG v) (hoppositeG v))
  change x.val ∈ F
  exact (PrescribedBlockCoordinates.prescribed_components_product j iota hsplit PA ρA n s labels T x) ▸ hp

include hρ hfρ hgρ hfbound hgbound hfpol hgpol hfdegree hgdegree hlabels hchosen in
theorem full_kernel_eq_from_chosen (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme) :
    a ≫ f.hom = 1 ↔ a ≫ g.hom = 1 :=
  ⟨full_kernel_imp_from_chosen j iota hsplit PA PB PC ρA ρB ρC hρ f g hfρ hgρ n
      hfbound hgbound hfpol hgpol hfdegree hgdegree s labels hlabels hchosen T a,
    full_kernel_imp_from_chosen j iota hsplit PA PC PB ρA ρC ρB hρ g f hgρ hfρ n
      hgbound hfbound hgpol hfpol hgdegree hfdegree s labels hlabels
      (fun v U x hs => (hchosen v U x hs).symm) T a⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ComparisonFromChosen
