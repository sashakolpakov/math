import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialLinearSquares
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateLocalHecke

/-! # Sl -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl.Local

noncomputable section

section

/-! Two homomorphic SL3 lifts with the same finite symplectic projection
agree exactly: the two-fold kernel disappears on squares. -/

open scoped Classical

theorem finite_sl3_lift_unique (q : ℕ) [Fact q.Prime]
    {I MpR MpF MpA : Type} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF)
    (hp : ∀ a, D.finite.project (f a) = D.finite.project (g a)) : f = g := by
  have hs (a : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) : f (a ^ 2) = g (a ^ 2) := by
    obtain ⟨ε, hε, ha⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finite_lifts_differ_by_sign D (f a) (g a) (hp a)
    apply D.finite.faithful
    apply Prod.ext
    · exact hp (a ^ 2)
    · apply LinearEquiv.ext
      intro φ
      change D.finite.action (f (a ^ 2)) φ = D.finite.action (g (a ^ 2)) φ
      rw [map_pow, map_pow, pow_two, pow_two, map_mul, map_mul]
      change D.finite.action (f a) (D.finite.action (f a) φ) =
        D.finite.action (g a) (D.finite.action (g a) φ)
      rw [ha, ha, map_smul, smul_smul, ← pow_two, hε, one_smul]
  have he : f.eqLocus g = ⊤ := SpecialLinearSquares.Local.specialLinear_generated_by_squares (f.eqLocus g) hs
  apply MonoidHom.ext
  intro a
  have hm : a ∈ f.eqLocus g := he ▸ Subgroup.mem_top a
  exact hm

theorem coordinateActiveLift_unique (q : ℕ) [Fact q.Prime]
    {Place : Type} [Fintype Place] [DecidableEq Place]
    {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF)
    (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF)
    (hf : ∀ g, D.finite.project (f g) =
      (D.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (ActiveBlockMatrices.Local.activeBlockGL e μ g)) *
        D.finite.project u) :
    f = CoordinateLocalHecke.coordinateActiveLift q e μ D u :=
  finite_sl3_lift_unique q D f (CoordinateLocalHecke.coordinateActiveLift q e μ D u)
    (fun g => (hf g).trans (CoordinateLocalHecke.coordinateActiveLift_projection q e μ D u g).symm)

end

section

/-! An away operator whose symplectic projection commutes with a local
SL3 lift commutes with the lift itself. The two-fold central kernel
introduces no character on SL3. -/

theorem finite_sl3_lift_commute (q : ℕ) [Fact q.Prime]
    {I MpR MpF MpA : Type} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF) (m : MpF)
    (h : ∀ g, Commute (D.finite.project m) (D.finite.project (f g))) :
    ∀ g, Commute m (f g) := by
  let f' := (MulAut.conj m).toMonoidHom.comp f
  have he : f' = f := finite_sl3_lift_unique q D f' f (by
    intro g
    change D.finite.project (m * f g * m⁻¹) = _
    rw [map_mul, map_mul, map_inv, (h g).eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one])
  intro g
  have he' : m * f g * m⁻¹ = f g := DFunLike.congr_fun he g
  exact mul_inv_eq_iff_eq_mul.mp he'

theorem finite_sl3_lift_centralizer (q : ℕ) [Fact q.Prime]
    {I MpR MpF MpA : Type} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF) (m : MpF) :
    (∀ g, Commute m (f g)) ↔
      ∀ g, Commute (D.finite.project m) (D.finite.project (f g)) := by
  constructor
  · intro h g
    exact (h g).map D.finite.project
  · exact finite_sl3_lift_commute q D f m

end

/-! Remove commuting local factors from a homomorphism without losing
the multiplication law. The full finite product of SL3 blocks has no
two-fold ambiguity, by restriction to each actual factor. -/

open scoped Classical

theorem finite_product_sl3_lift_unique (q : ℕ) [Fact q.Prime]
    {J : Type} [Fintype J] [DecidableEq J]
    {I MpR MpF MpA : Type} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f g : (J → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) →* MpF)
    (hp : ∀ a, D.finite.project (f a) = D.finite.project (g a)) : f = g := by
  apply MonoidHom.pi_ext
  intro j a
  exact DFunLike.congr_fun (finite_sl3_lift_unique q D
    (f.comp (MonoidHom.mulSingle (fun _ : J => RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) j))
    (g.comp (MonoidHom.mulSingle (fun _ : J => RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) j))
    (fun b => hp (Pi.mulSingle j b))) a

theorem finite_product_sl3_lift_commute (q : ℕ) [Fact q.Prime]
    {J : Type} [Fintype J] [DecidableEq J]
    {I MpR MpF MpA : Type} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f : (J → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) →* MpF) (m : MpF)
    (h : ∀ g, Commute (D.finite.project m) (D.finite.project (f g))) :
    ∀ g, Commute m (f g) := by
  let f' := (MulAut.conj m).toMonoidHom.comp f
  have he : f' = f := finite_product_sl3_lift_unique q D f' f (by
    intro g
    change D.finite.project (m * f g * m⁻¹) = _
    rw [map_mul, map_mul, map_inv, (h g).eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one])
  intro g
  have he' : m * f g * m⁻¹ = f g := DFunLike.congr_fun he g
  exact mul_inv_eq_iff_eq_mul.mp he'

def commutingResidualHom {G H : Type} [Group G] [Group H]
    (f l : G →* H) (hc : ∀ g h, Commute (f g * (l g)⁻¹) (l h)) : G →* H where
  toFun g := f g * (l g)⁻¹
  map_one' := by simp
  map_mul' g h := by
    calc
      f (g * h) * (l (g * h))⁻¹ = f g * (f h * (l h)⁻¹) * (l g)⁻¹ := by
        simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = f g * (l g)⁻¹ * (f h * (l h)⁻¹) := by
        rw [mul_assoc, (hc h g).inv_right.eq, ← mul_assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl.Local
