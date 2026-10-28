import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

/-! # Line Frame Atlas -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

noncomputable section

section

/-! All actual local frames of a line-bundle sheaf form an atlas. Its
transition units commute with restriction. Using all frames permits
tensor and pullback comparisons without synchronizing arbitrary choices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

variable {X : Scheme.{0}}

structure LocalLineFrame (M : X.Modules) where
  domain : X.Opens
  frame : M.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme

namespace LocalLineFrame

variable {M N : X.Modules}

def coordinates (s : LocalLineFrame M) (U : X.Opens) (hU : U ≤ s.domain) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) := DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M s.domain s.frame U hU

theorem coordinates_restrict (s : LocalLineFrame M) {U V : X.Opens}
    (hVU : V ≤ U) (hU : U ≤ s.domain) (x : Γ(M, U)) :
    s.coordinates V (hVU.trans hU) (M.presheaf.map (homOfLE hVU).op x) =
      X.presheaf.map (homOfLE hVU).op (s.coordinates U hU x) :=
  DivisorClass.Chern.FramesFrame.Construction.frameOnOpen_naturality M s.domain s.frame hVU hU x

def transition (s t : LocalLineFrame M) (U : X.Opens) (hs : U ≤ s.domain) (ht : U ≤ t.domain) :
    Γ(X, U)ˣ := DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (s.coordinates U hs) (t.coordinates U ht)

theorem transition_restrict (s t : LocalLineFrame M) {U V : X.Opens}
    (hVU : V ≤ U) (hs : U ≤ s.domain) (ht : U ≤ t.domain) :
    Units.map (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom (s.transition t U hs ht) =
      s.transition t V (hVU.trans hs) (hVU.trans ht) :=
  DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_map (X.presheaf.map (homOfLE hVU).op).hom
    (M.presheaf.map (homOfLE hVU).op) _ _ _ _
    (s.coordinates_restrict hVU hs) (t.coordinates_restrict hVU ht)

theorem transition_cocycle (s t r : LocalLineFrame M) (U : X.Opens)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain) (hr : U ≤ r.domain) :
    s.transition t U hs ht * t.transition r U ht hr = s.transition r U hs hr :=
  DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _

def tensor (s : LocalLineFrame M) (t : LocalLineFrame N) : LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) where
  domain := s.domain ⊓ t.domain
  frame := HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso (s.domain ⊓ t.domain).ι M N ≪≫
    SheafTensorFrames.tensorSheafFrame (DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization s.frame inf_le_left)
      (DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization t.frame inf_le_right)

end LocalLineFrame

theorem localLineFrames_cover (L : HilbertConstruction.Line.Bundles.LineBundle X) (x : X) :
    ∃ s : LocalLineFrame L.sheaf, x ∈ s.domain := by
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  exact ⟨⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e⟩, hx⟩

end

/-! Literal local coefficients of an algebraic line-sheaf morphism,
their restriction law, and their change-of-frame identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem rankOne_coordinate_expansion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (x : M) : x = e x • e.symm 1 := by
  apply e.injective
  rw [e.map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]

theorem rankOneLinearMap_coefficient {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M ≃ₗ[R] R) (g : N ≃ₗ[R] R) (x : M) :
    g (f x) = e x * g (f (e.symm 1)) := by
  calc
    g (f x) = g (f (e x • e.symm 1)) := congrArg (fun y => g (f y)) (rankOne_coordinate_expansion e x)
    _ = _ := by rw [f.map_smul, g.map_smul, smul_eq_mul]

theorem rankOneLinearMap_frame_change {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e₀ e₁ : M ≃ₗ[R] R) (g₀ g₁ : N ≃ₗ[R] R) :
    (DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e₀ e₁ : R) * g₀ (f (e₀.symm 1)) =
      g₁ (f (e₁.symm 1)) * (DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit g₀ g₁ : R) :=
  (rankOneLinearMap_coefficient f e₀ g₀ (e₁.symm 1)).symm.trans
    (rankOneLinearMap_coefficient LinearMap.id g₁ g₀ (f (e₁.symm 1)))

variable {X : Scheme.{0}} {M N : X.Modules}

def lineMorphismCoefficient (f : M ⟶ N) (r : LocalLineFrame M) (s : LocalLineFrame N)
    (U : X.Opens) (hr : U ≤ r.domain) (hs : U ≤ s.domain) : Γ(X, U) :=
  s.coordinates U hs (f.app U ((r.coordinates U hr).symm 1))

theorem lineMorphismCoefficient_restrict (f : M ⟶ N) (r : LocalLineFrame M) (s : LocalLineFrame N)
    {U V : X.Opens} (h : V ≤ U) (hr : U ≤ r.domain) (hs : U ≤ s.domain) :
    lineMorphismCoefficient f r s V (h.trans hr) (h.trans hs) =
      X.presheaf.map (homOfLE h).op (lineMorphismCoefficient f r s U hr hs) := by
  have he : M.presheaf.map (homOfLE h).op ((r.coordinates U hr).symm 1) =
      (r.coordinates V (h.trans hr)).symm 1 := by
    apply (r.coordinates V (h.trans hr)).injective
    rw [r.coordinates_restrict h hr, LinearEquiv.apply_symm_apply, map_one, LinearEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op)
    ((r.coordinates U hr).symm 1)
  change f.app V (M.presheaf.map (homOfLE h).op ((r.coordinates U hr).symm 1)) =
    N.presheaf.map (homOfLE h).op (f.app U ((r.coordinates U hr).symm 1)) at hn
  exact (congrArg (fun y => s.coordinates V (h.trans hs) (f.app V y)) he.symm).trans
    ((congrArg (s.coordinates V (h.trans hs)) hn).trans
      (s.coordinates_restrict h hs (f.app U ((r.coordinates U hr).symm 1))))

theorem lineMorphismCoefficient_frame_change (f : M ⟶ N)
    (r₀ r₁ : LocalLineFrame M) (s₀ s₁ : LocalLineFrame N) (U : X.Opens)
    (hr₀ : U ≤ r₀.domain) (hr₁ : U ≤ r₁.domain) (hs₀ : U ≤ s₀.domain) (hs₁ : U ≤ s₁.domain) :
    (r₀.transition r₁ U hr₀ hr₁ : Γ(X, U)) * lineMorphismCoefficient f r₀ s₀ U hr₀ hs₀ =
      lineMorphismCoefficient f r₁ s₁ U hr₁ hs₁ * (s₀.transition s₁ U hs₀ hs₁ : Γ(X, U)) :=
  rankOneLinearMap_frame_change (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U)
    (r₀.coordinates U hr₀) (r₁.coordinates U hr₁) (s₀.coordinates U hs₀) (s₁.coordinates U hs₁)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
