import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionDivisionNe

/-! # Stalk Ideal Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealFrame.Construction.StalkIdealFrames

noncomputable section

/-! A nonzero principal stalk-ideal generator gives an actual local sheaf frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (I : ∀ x : X, Ideal (X.presheaf.stalk x))

def multiply {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U))
    (ha : a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal I U) :
    Γ(X, V) →ₗ[Γ(X, V)] Γ(StalkIdealIs.Construction.StalkIdealSheaf.sheaf I, V) where
  toFun s := ⟨X.presheaf.map (homOfLE h).op a * s, by
    apply (StalkIdealIs.Construction.StalkIdealSheaf.mem_ideal I V _).mpr
    intro x
    rw [map_mul, X.presheaf.germ_res_apply]
    exact (I x).mul_mem_right _
      ((StalkIdealIs.Construction.StalkIdealSheaf.mem_ideal I U a).mp ha ⟨x, h x.2⟩)⟩
  map_add' s t := by
    apply Subtype.ext
    exact mul_add (X.presheaf.map (homOfLE h).op a) s t
  map_smul' r s := by
    apply Subtype.ext
    change _ * (r * s) = r * (_ * s)
    exact mul_left_comm _ _ _

theorem multiply_natural {U V W : X.Opens} (hV : V ≤ U) (hW : W ≤ V)
    (a : Γ(X, U)) (ha : a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal I U) (s : Γ(X, V)) :
    (StalkIdealIs.Construction.StalkIdealSheaf.sheaf I).presheaf.map (homOfLE hW).op (multiply I hV a ha s) =
      multiply I (hW.trans hV) a ha (X.presheaf.map (homOfLE hW).op s) := by
  apply Subtype.ext
  change X.presheaf.map (homOfLE hW).op (X.presheaf.map (homOfLE hV).op a * s) = _
  rw [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def frameMap (U : X.Opens) (a : Γ(X, U)) (ha : a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal I U) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι ⟶ (StalkIdealIs.Construction.StalkIdealSheaf.sheaf I).restrict U.ι where
  val.app W := ModuleCat.ofHom
    (X := ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι).val.obj W)
    (Y := ((StalkIdealIs.Construction.StalkIdealSheaf.sheaf I).restrict U.ι).val.obj W) (show
    Γ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).restrict U.ι, W.unop) →ₗ[Γ(U.toScheme, W.unop)]
      Γ((StalkIdealIs.Construction.StalkIdealSheaf.sheaf I).restrict U.ι, W.unop) from
    { toFun s := multiply I (U.ι_image_le W.unop) a ha
        (show Γ(X, U.ι ''ᵁ W.unop) from s)
      map_add' s t := (multiply I (U.ι_image_le W.unop) a ha).map_add
        (show Γ(X, U.ι ''ᵁ W.unop) from s) (show Γ(X, U.ι ''ᵁ W.unop) from t)
      map_smul' r s := by
        change Γ(X, U.ι ''ᵁ W.unop) at s
        apply Subtype.ext
        change _ * ((U.ι.appIso W.unop).inv r * s) =
          (U.ι.appIso W.unop).inv r * (_ * s)
        exact mul_left_comm _ _ _ })
  val.naturality {V W} h := by
    ext s
    exact (multiply_natural I (U.ι_image_le V.unop)
      (U.ι.image_mono h.unop.le) a ha s).symm

theorem multiply_bijective [IsIntegral X] {U V : X.Opens} (hV : V ≤ U)
    (a : Γ(X, U)) (ha : a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal I U) (ha0 : a ≠ 0)
    (hgen : ∀ x : U, I x = Ideal.span {X.presheaf.germ U x x.2 a}) :
    Function.Bijective (multiply I hV a ha) := by
  constructor
  · intro s t hst
    exact SectionDivisionNe.Construction.SectionDivision.cancel_restrict hV ha0 (congrArg Subtype.val hst)
  · intro s
    by_cases hVne : Nonempty V
    · have := hVne
      have hd : X.presheaf.map (homOfLE hV).op a ∣ s.val := by
        apply SectionDivisionNe.Construction.SectionDivision.dvd_of_germs _ _ (SectionDivisionNe.Construction.SectionDivision.restrict_ne_zero hV ha0)
        intro x
        have hs := (StalkIdealIs.Construction.StalkIdealSheaf.mem_ideal I V s.val).mp s.property x
        rw [hgen ⟨x, hV x.2⟩, Ideal.mem_span_singleton] at hs
        rwa [X.presheaf.germ_res_apply]
      obtain ⟨t, ht⟩ := hd
      exact ⟨t, Subtype.ext ht.symm⟩
    · have hbot : V = ⊥ := by
        apply SetLike.ext
        intro x
        exact ⟨fun hx => (hVne ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
      have : Subsingleton Γ(X, V) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
      refine ⟨0, Subtype.ext ?_⟩
      change (X.presheaf.map (homOfLE hV).op a * 0 : Γ(X, V)) = s.val
      exact Subsingleton.elim _ _

def frameIso [IsIntegral X] (U : X.Opens) (a : Γ(X, U))
    (ha : a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal I U) (ha0 : a ≠ 0)
    (hgen : ∀ x : U, I x = Ideal.span {X.presheaf.germ U x x.2 a}) :
    (Scheme.Modules.pullback U.ι).obj (StalkIdealIs.Construction.StalkIdealSheaf.sheaf I) ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme := by
  have : IsIso (frameMap I U a ha) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    apply (ConcreteCategory.isIso_iff_bijective ((frameMap I U a ha).app W)).mpr
    exact multiply_bijective I (U.ι_image_le W) a ha ha0 hgen
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
    (asIso (frameMap I U a ha)).symm ≪≫ Scheme.Modules.restrictUnitIso U.ι

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealFrame.Construction.StalkIdealFrames
