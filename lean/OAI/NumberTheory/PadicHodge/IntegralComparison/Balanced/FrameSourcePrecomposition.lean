import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourceNormalization

/-! # Frame Source Precomposition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourcePrecomposition

noncomputable section

/-! Source normalization with an arbitrary incoming complex, before
specializing the coefficient resolution to a sheafified Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (K : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ)
  (M : CochainComplex (ModuleCat.{max u z} R) ℕ)
  (s : M ⟶ ResolutionHom.Total.sections R
    (Z := Ext.ZeroPresheafSections.constantUnit R J) K)

local instance coproducts : HasCoproducts.{0} (ModuleCat.{max u z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{max u z,u,0,0} R).has_colimits_of_shape (Discrete T)

def liftedMap := s ≫ FrameSourceNormalization.edge F R J K

private theorem coordinate_precomp {A : Type*} [Category A] {V W B C D T : A}
    (s : V ⟶ W) (a : W ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : W ⟶ T) (e : T ⟶ D) (t : V ⟶ D)
    (h : (a ≫ b) ≫ c = d ≫ e) (ht : s ≫ d ≫ e = t) :
    (s ≫ (a ≫ b)) ≫ c = t := by
  rw [Category.assoc, h]
  exact ht

theorem square
    (t : M ⟶ ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).obj
      ((FrameCech.IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,0} F R J K).total (.up ℕ)))
    (ht : s ≫ (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom ≫
      ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
        (FrameCech.GlobalEdge.nativeEdge F R J K) = t) :
    liftedMap F R J K M s ≫
      (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).hom = t :=
  coordinate_precomp s _ _ _ _ _ t (FrameCech.GlobalEdge.coordinates F R J K) ht

private theorem map_precomp {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {X Y Z W : A} {T : B} (f : X ⟶ Y) (a : Y ⟶ Z)
    (b : Y ⟶ W) (c : G.obj Z ⟶ T) (d : G.obj W ⟶ T)
    (h : G.map a ≫ c = G.map b ≫ d) :
    G.map (f ≫ a) ≫ c = G.map (f ≫ b) ≫ d := by
  simp only [G.map_comp, Category.assoc]
  rw [h]

variable (hcover : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ J V)
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y) (g : K ⟶ I.cocomplex)

/-- The comparison after applying homology to the lifted incoming map. -/
def homologyLeft (i : ℕ) :=
  HomologicalComplex.homologyMap (liftedMap F R J K M s) i ≫
    FrameAugmentation.comparison F R J hcover I K g i

/-- The same incoming map followed by the injective section comparison. -/
def homologyRight (i : ℕ) :=
  HomologicalComplex.homologyMap (s ≫ ResolutionHom.SourceNaturality.sectionsMap R g) i ≫
    (InjectiveSectionCohomology.homologyIso R
      (Ext.ZeroPresheafSections.constantUnit R J) I i).hom

omit [Finite ι] in
/-- Source-normalized homology after precomposition by the incoming map. -/
theorem homology (i : ℕ) :
    homologyLeft F R J K M s hcover I g i = homologyRight R J K M s I g i := by
  exact map_precomp
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u z} R) (.up ℕ) i)
    s (FrameSourceNormalization.edge F R J K)
    (ResolutionHom.SourceNaturality.sectionsMap R g)
    (FrameAugmentation.comparison F R J hcover I K g i)
    (InjectiveSectionCohomology.homologyIso R
      (Ext.ZeroPresheafSections.constantUnit R J) I i).hom
    (FrameSourceNormalization.source_homology F R J hcover I K g i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameSourcePrecomposition
