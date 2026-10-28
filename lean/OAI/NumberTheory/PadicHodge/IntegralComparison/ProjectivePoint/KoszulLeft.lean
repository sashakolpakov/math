import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap

/-! # Koszul Left -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulLeft

noncomputable section

/-! The left leg of the original common negative refinement induces
the identity local normal-Koszul map, by an actual cochain homotopy.
Together with the right leg this normalizes the full refinement zigzag. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulMap
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Z X : Scheme.{u}} (s₀ : Z ⟶ X)
  (f : X ⟶ Proj (homogeneousSubmodule σ R))
  [IsClosedImmersion s₀] [IsClosedImmersion f]
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : σ) (B : ℕ)

local instance scalar_qc : (KoszulMap.scalar f).IsQuasicoherent :=
  IntegralComparison.Projective.ClosedImmersionPurity.directImage_quasicoherent f
local instance scalar_finite : (KoszulMap.scalar f).IsFiniteType :=
  IntegralComparison.Projective.ClosedImmersionPurity.directImage_finiteType f
local instance point_qc : (KoszulMap.point s₀ f).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent s₀ f
local instance point_finite : (KoszulMap.point s₀ f).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType s₀ f
local instance common_qc (q : ℕ) : ((KoszulMap.common s₀ f j B).X q).IsQuasicoherent :=
  IntegralComparison.Projective.NegativeRefinement.term_quasicoherent (KoszulMap.scalar f) (KoszulMap.point s₀ f) j B (KoszulMap.quotientMap s₀ f) q

variable (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Proj (homogeneousSubmodule σ R), U)] Γ(Proj (homogeneousSubmodule σ R), U))
  {c : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule σ R), U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule σ R), U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U) (List.ofFn s))

abbrev leftHomotopy := by
  let K := IntegralComparison.Projective.NegativeResolution.complex (KoszulMap.scalar f) j B
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((KoszulMap.common s₀ f j B).X q)) :=
    KoszulMap.common_projective s₀ f U hU i hi j B q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hi (KoszulMap.scalar f) j B q
  let ε := IntegralComparison.Projective.NegativeRefinement.augmentation (KoszulMap.scalar f) (KoszulMap.point s₀ f) j B (KoszulMap.quotientMap s₀ f)
  let ε' := IntegralComparison.Projective.NegativeResolution.augmentation (KoszulMap.scalar f) j B
  let v := (IntegralComparison.Projective.NegativeRefinement.leftHom (KoszulMap.scalar f) (KoszulMap.point s₀ f) j B (KoszulMap.quotientMap s₀ f)).chainMap
  let eM := Principal.OrientedResidue.quotientIso f U hU s hs
  let P := KoszulPartial.Resolution.normalResolution _ s hreg
  let hv := Principal.ResolutionAugmentation.square U hU (KoszulMap.scalar f) (KoszulMap.common s₀ f j B) ε _ eM
    (KoszulMap.scalar f) K ε' _ eM v (𝟙 (KoszulMap.scalar f)) (𝟙 _)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      IntegralComparison.Projective.NegativeRefinement.left_augmentation (KoszulMap.scalar f) (KoszulMap.point s₀ f) j B (KoszulMap.quotientMap s₀ f))
    (by simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  exact Principal.Resolution.Comparison.naturality U hU N e
    (KoszulMap.scalar f) (KoszulMap.common s₀ f j B) ε _ eM P
    (KoszulMap.scalar f) K ε' _ eM P v (𝟙 _) (𝟙 P.complex) hv
    (by simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.KoszulLeft
