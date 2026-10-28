import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo

/-! # Semilinear Derived Q -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearDerivedQ.SemilinearDerived

noncomputable section

/-! Exact functors carry their actual scalar action to derived morphism spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w w'

section Basic

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear S D]
  (F : C ⥤ D)

theorem map_smul_of_identity
    (h : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
    {X Y : C} (f : X ⟶ Y) (r : R) : F.map (r • f) = σ r • F.map f := by
  calc
    F.map (r • f) = F.map (f ≫ (r • 𝟙 Y)) := by rw [Linear.comp_smul, Category.comp_id]
    _ = F.map f ≫ (σ r • 𝟙 (F.obj Y)) := by rw [F.map_comp, h]
    _ = σ r • F.map f := by rw [Linear.comp_smul, Category.comp_id]

theorem scalar_identity_of_iso {X Y : C} (e : X ≅ Y) (r : R)
    (h : F.map (r • 𝟙 X) = σ r • 𝟙 (F.obj X)) :
    F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y) := by
  apply (cancel_mono (F.map e.inv)).mp
  calc
    F.map (r • 𝟙 Y) ≫ F.map e.inv = F.map ((r • 𝟙 Y) ≫ e.inv) := (F.map_comp _ _).symm
    _ = F.map (e.inv ≫ (r • 𝟙 X)) := by rw [Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
    _ = F.map e.inv ≫ (σ r • 𝟙 (F.obj X)) := by rw [F.map_comp, h]
    _ = (σ r • 𝟙 (F.obj Y)) ≫ F.map e.inv := by
      rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

end Basic

section HomEquivalence

variable {R S : Type*} [Field R] [Field S] (σ : R ≃+* S)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear S D]
  (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]

def homEquiv
    (h : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
    (X Y : C) : (X ⟶ Y) ≃ₛₗ[σ.toRingHom] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective
    { __ := F.mapAddHom
      map_smul' r f := map_smul_of_identity σ.toRingHom F h f r }
    ⟨F.map_injective, F.map_surjective⟩

end HomEquivalence

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [Linear S D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (h : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))

include h

omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem complex_scalar_identity (K : CochainComplex C ℤ) (r : R) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 K) =
      σ r • 𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact h (K.X i) r

theorem derived_scalar_identity_Q (K : CochainComplex C ℤ) (r : R) :
    F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj K)) =
      σ r • 𝟙 (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app K)).mp
  have hn := F.mapDerivedCategoryFactors_hom_naturality (r • 𝟙 K)
  rw [DerivedCategory.Q.map_smul r (𝟙 K), DerivedCategory.Q.map_id,
    complex_scalar_identity σ F h, DerivedCategory.Q.map_smul (σ r),
    DerivedCategory.Q.map_id] at hn
  rw [Linear.smul_comp, Category.id_comp]
  exact hn.trans ((Linear.comp_smul _ _ _ _ _ _).trans
    (congrArg (fun f => σ r • f) (Category.comp_id _)))

theorem derived_scalar_identity (Y : DerivedCategory C) (r : R) :
    F.mapDerivedCategory.map (r • 𝟙 Y) = σ r • 𝟙 (F.mapDerivedCategory.obj Y) :=
  scalar_identity_of_iso σ F.mapDerivedCategory (DerivedCategory.Q.objObjPreimageIso Y) r
    (derived_scalar_identity_Q σ F h (DerivedCategory.Q.objPreimage Y) r)

theorem derived_map_smul {X Y : DerivedCategory C} (f : X ⟶ Y) (r : R) :
    F.mapDerivedCategory.map (r • f) = σ r • F.mapDerivedCategory.map f :=
  map_smul_of_identity σ F.mapDerivedCategory (derived_scalar_identity σ F h) f r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearDerivedQ.SemilinearDerived
