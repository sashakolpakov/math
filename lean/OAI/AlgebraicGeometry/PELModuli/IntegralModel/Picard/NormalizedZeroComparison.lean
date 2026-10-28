import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizationRestriction

/-! # Normalized Zero Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison

noncomputable section

/-! Checked import adaptation of `/Proofs/NormalizedZeroComparison.lean`; original.
Only imports and namespaces change. -/

/-! The concrete trivialization equation supplies the intrinsic comparison
between the two zero fibers used for restriction and descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

theorem square_to_conjugated_equality {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ U V : C} (a₁ : A₁ ≅ U) (a₂ : A₂ ≅ U)
    (b₁ : B₁ ≅ V) (b₂ : B₂ ≅ V) (q₁ : A₁ ⟶ B₁) (q₂ : A₂ ⟶ B₂)
    (h : q₁ ≫ (b₁ ≪≫ b₂.symm).hom = (a₁ ≪≫ a₂.symm).hom ≫ q₂) :
    a₁.inv ≫ q₁ ≫ b₁.hom = a₂.inv ≫ q₂ ≫ b₂.hom := by
  have hh := congrArg (fun q ↦ a₁.inv ≫ q ≫ b₂.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh

variable {X V T B : Scheme.{u}} {M N : X.Modules}
variable (s : V ⟶ X) (z : B ⟶ X) (zt : T ⟶ V) (t : T ⟶ B) (h : zt ≫ s = t ≫ z)
variable (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule B)
variable (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule B)

theorem normalized_zero_square
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (hq : (Scheme.Modules.pullback zt).map q ≫ (NormalizedSquares.PicardNormalizedSquares.squareZeroIso s z zt t h eN).hom =
      (NormalizedSquares.PicardNormalizedSquares.squareZeroIso s z zt t h eM).hom) :
    (Scheme.Modules.pullback zt).map q ≫ (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso s z zt t h).hom.app N =
      (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso s z zt t h).hom.app M ≫
        (Scheme.Modules.pullback t).map (eM.hom ≫ eN.inv) := by
  let L := Scheme.Modules.pullback t
  let α := NormalizedSquares.PicardNormalizedSquares.sectionSquareIso s z zt t h
  let v := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso t
  apply (cancel_mono (L.map eN.hom ≫ v.hom)).mp
  have hr : (α.hom.app M ≫ L.map (eM.hom ≫ eN.inv)) ≫ (L.map eN.hom ≫ v.hom) =
      (NormalizedSquares.PicardNormalizedSquares.squareZeroIso s z zt t h eM).hom := by
    change (α.hom.app M ≫ L.map (eM.hom ≫ eN.inv)) ≫ (L.map eN.hom ≫ v.hom) =
      α.hom.app M ≫ L.map eM.hom ≫ v.hom
    rw [L.map_comp]
    have hn : L.map eN.inv ≫ L.map eN.hom = 𝟙 _ := (L.mapIso eN).inv_hom_id
    simp only [Category.assoc]
    rw [← Category.assoc (L.map eN.inv) (L.map eN.hom), hn, Category.id_comp]
  exact (Category.assoc _ _ _).trans (hq.trans hr.symm)

/-- This is the normalization equation in the actual pullback
pseudofunctor, derived from the concrete zero trivializations. -/
theorem normalized_zero_intrinsic
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (hq : (Scheme.Modules.pullback zt).map q ≫ (NormalizedSquares.PicardNormalizedSquares.squareZeroIso s z zt t h eN).hom =
      (NormalizedSquares.PicardNormalizedSquares.squareZeroIso s z zt t h eM).hom) :
    Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      z t s zt h q (eM.hom ≫ eN.inv) := by
  let c₁ := Scheme.Modules.pullbackComp zt s ≪≫ Scheme.Modules.pullbackCongr h
  let c₂ := Scheme.Modules.pullbackComp t z
  have hs := normalized_zero_square s z zt t h eM eN q hq
  have hc := square_to_conjugated_equality (c₁.app M) (c₂.app M) (c₁.app N) (c₂.app N)
    ((Scheme.Modules.pullback zt).map q) ((Scheme.Modules.pullback t).map (eM.hom ≫ eN.inv)) hs
  have h₁ := Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom zt s (t ≫ z) h q
  have h₂ := Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom t z (t ≫ z) rfl (eM.hom ≫ eN.inv)
  exact h₁.symm.trans (hc.trans h₂)

def NativeNormalized
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N) : Prop :=
  Isogenies.NeighborCounting.FramedPullback.pullbackHomTo zt s (t ≫ z) h q = Isogenies.NeighborCounting.FramedPullback.pullbackHomTo t z (t ≫ z) rfl q₀

theorem nativeNormalized_iff_intrinsic
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N) :
    NativeNormalized s z zt t h q q₀ ↔
      Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) z t s zt h q q₀ := by
  unfold NativeNormalized Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized
  rw [Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom, Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom]
  rfl

theorem intrinsic_normalization_restrict {T' V' : Scheme.{u}}
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N)
    (hq : Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) z t s zt h q q₀)
    (a : V' ⟶ V) (b : T' ⟶ T) (t' : T' ⟶ B) (s' : V' ⟶ X) (zt' : T' ⟶ V')
    (ht : b ≫ t = t') (hs : a ≫ s = s') (hz : zt' ≫ a = b ≫ zt)
    (h' : zt' ≫ s' = t' ≫ z) :
    Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      z t' s' zt' h' (Isogenies.NeighborCounting.FramedPullback.pullbackHomTo a s s' hs q) q₀ := by
  have hn := Isogenies.NeighborCounting.NormalizationRestriction.normalized_restrict
    (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) z t s zt h q q₀ hq a b t' s' zt' ht hs hz h'
  have hp := Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom a s s' hs q
  exact (congrArg (fun r ↦ Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized
    (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) z t' s' zt' h' r q₀) hp).mpr hn

theorem intrinsic_normalization_restrict_iso {T' V' : Scheme.{u}}
    (e : (Scheme.Modules.pullback s).obj M ≅ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N)
    (hq : Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) z t s zt h e.hom q₀)
    (a : V' ⟶ V) (b : T' ⟶ T) (t' : T' ⟶ B) (s' : V' ⟶ X) (zt' : T' ⟶ V')
    (ht : b ≫ t = t') (hs : a ≫ s = s') (hz : zt' ≫ a = b ≫ zt)
    (h' : zt' ≫ s' = t' ≫ z) :
    Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      z t' s' zt' h' (Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo a s s' hs e).hom q₀ := by
  rw [Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo_hom]
  exact intrinsic_normalization_restrict s z zt t h e.hom q₀ hq a b t' s' zt' ht hs hz h'

theorem native_normalization_restrict {T' V' : Scheme.{u}}
    (q : (Scheme.Modules.pullback s).obj M ⟶ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N)
    (hq : NativeNormalized s z zt t h q q₀)
    (a : V' ⟶ V) (b : T' ⟶ T) (t' : T' ⟶ B) (s' : V' ⟶ X) (zt' : T' ⟶ V')
    (ht : b ≫ t = t') (hs : a ≫ s = s') (hz : zt' ≫ a = b ≫ zt)
    (h' : zt' ≫ s' = t' ≫ z) :
    NativeNormalized s' z zt' t' h' (Isogenies.NeighborCounting.FramedPullback.pullbackHomTo a s s' hs q) q₀ :=
  (nativeNormalized_iff_intrinsic s' z zt' t' h' _ q₀).mpr
    (intrinsic_normalization_restrict s z zt t h q q₀
      ((nativeNormalized_iff_intrinsic s z zt t h q q₀).mp hq)
      a b t' s' zt' ht hs hz h')

theorem native_normalization_restrict_iso {T' V' : Scheme.{u}}
    (e : (Scheme.Modules.pullback s).obj M ≅ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N)
    (hq : NativeNormalized s z zt t h e.hom q₀)
    (a : V' ⟶ V) (b : T' ⟶ T) (t' : T' ⟶ B) (s' : V' ⟶ X) (zt' : T' ⟶ V')
    (ht : b ≫ t = t') (hs : a ≫ s = s') (hz : zt' ≫ a = b ≫ zt)
    (h' : zt' ≫ s' = t' ≫ z) :
    NativeNormalized s' z zt' t' h' (Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo a s s' hs e).hom q₀ := by
  rw [Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo_hom]
  exact native_normalization_restrict s z zt t h e.hom q₀ hq a b t' s' zt' ht hs hz h'

theorem iso_eq_of_intrinsic_normalization
    (π : V ⟶ T) (hπ : zt ≫ π = 𝟙 T) (hΓ : Function.Surjective π.appTop)
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle ((Scheme.Modules.pullback s).obj M))
    (e f : (Scheme.Modules.pullback s).obj M ≅ (Scheme.Modules.pullback s).obj N)
    (q₀ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback z).obj N)
    (he : Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      z t s zt h e.hom q₀)
    (hf : Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      z t s zt h f.hom q₀) : e = f := by
  apply RigidifiedUniqueness.PicardRigidifiedUniqueness.iso_eq_of_section π zt hπ hΓ hM e f
  let c := Scheme.Modules.pullbackComp zt s ≪≫ Scheme.Modules.pullbackCongr h
  apply ((c.app M).homCongr (c.app N)).injective
  dsimp only [Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized] at he hf
  exact (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom zt s (t ≫ z) h e.hom).trans
    ((he.trans hf.symm).trans (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom zt s (t ≫ z) h f.hom).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison
