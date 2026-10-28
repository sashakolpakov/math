import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq

/-! # Ample Fiber Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleFiberEq.Construction.AmpleFiber

noncomputable section

/-! Proper connected fibers inside an open trivializing an ample line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem scalar_nonvanishing_eq_bot_or_top {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = ⊥ ∨ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = ⊤ := by
  rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar]
  rcases ProperFunctionsEq.Construction.ProperFunctions.section_eq_zero_or_isUnit X (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X.left a) with h | h
  · exact Or.inl (h ▸ X.left.basicOpen_zero ⊤)
  · exact Or.inr (X.left.basicOpen_of_isUnit h)

theorem preimage_nonvanishing_eq_bot_or_top {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {A : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (W : A.Opens)
    (e : (L.pullback W.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme)
    (g : X.left ⟶ W.toScheme) (m : ℕ)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A ⟶ (L.tensorPower m).sheaf) :
    (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊥ ∨
      (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  let e' : (Scheme.Modules.pullback W.ι).obj (L.tensorPower m).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme :=
    L.tensorPowerPullbackIso m W.ι ≪≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor W.toScheme m).mapIso e ≪≫
      AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso W.toScheme m
  let t : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme) := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection W.ι s ≫ e'.hom
  let a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) :=
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g t ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom
  have ha : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, PullbackScalarsValue.Construction.PullbackScalars.nonvanishing_pullback_scalar]
    dsimp only [t]
    rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback W.ι]
    rfl
  rw [← ha]
  exact scalar_nonvanishing_eq_bot_or_top X a

/-- An ample section neighborhood containing one image point contains the
whole proper connected reduced source when the bundle is trivial along that source's open. -/
theorem exists_affine_contains_image {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {A : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (hL : L.IsAmple) (W : A.Opens)
    (e : (L.pullback W.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme)
    (g : X.left ⟶ W.toScheme) :
    ∃ V : A.Opens, IsAffineOpen V ∧ Set.range (g ≫ W.ι) ⊆ V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X.left)
  obtain ⟨m, _hm, s, hx, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 ((g ≫ W.ι) x)
  refine ⟨AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s, hs, ?_⟩
  have ht : (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ :=
    (preimage_nonvanishing_eq_bot_or_top X L W e g m s).resolve_left (by
      intro h
      have hx' : x ∈ (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := hx
      rw [h] at hx'
      exact hx'.elim)
  rintro _ ⟨y, rfl⟩
  exact (show y ∈ (g ≫ W.ι) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s from ht.symm ▸ trivial)

theorem apply_eq {K : Type u} [Field K]
    (X A : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    [LocallyOfFiniteType A.hom] [IsSeparated A.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple) (W : A.left.Opens)
    (e : (L.pullback W.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme)
    (f : X ⟶ A) (g : X.left ⟶ W.toScheme) (hg : g ≫ W.ι = f.left)
    (x y : X.left) : f.left x = f.left y := by
  obtain ⟨V, hV, h⟩ := exists_affine_contains_image X L hL W e g
  have hr : Set.range f.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, ← hg]
    exact h
  let q := IsOpenImmersion.lift V.ι f.left hr
  have hq : q ≫ V.ι = f.left := IsOpenImmersion.lift_fac V.ι f.left hr
  let B : Over (Spec (.of K)) := Over.mk (V.ι ≫ A.hom)
  have : IsAffine B.left := hV
  have : LocallyOfFiniteType B.hom := by dsimp [B]; infer_instance
  have : IsSeparated B.hom := by dsimp [B]; infer_instance
  let q' : X ⟶ B := Over.homMk q (by
    change q ≫ V.ι ≫ A.hom = X.hom
    rw [← Category.assoc, hq, Over.w])
  have he := ProperFunctionsEq.Construction.ProperFunctions.apply_eq q' x y
  have hx : V.ι (q x) = f.left x := congrArg (fun k => k x) hq
  have hy : V.ι (q y) = f.left y := congrArg (fun k => k y) hq
  exact hx.symm.trans ((congrArg V.ι he).trans hy)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleFiberEq.Construction.AmpleFiber
