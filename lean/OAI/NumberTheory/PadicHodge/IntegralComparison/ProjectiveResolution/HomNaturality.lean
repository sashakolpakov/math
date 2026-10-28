import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Hom

/-! # Hom Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomNaturality

noncomputable section

/-! The ordinary-Hom comparison between projective resolutions is natural
for every lift of a map of the original resolved objects. -/

open _root_.CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false

universe u v w z

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive]

def functor : (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex D ℕ :=
  HomologicalComplex.opFunctor C (.down ℕ) ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ).symm

def map {P Q : ChainComplex C ℕ} (a : P ⟶ Q) (n : ℕ) :=
  HomologicalComplex.homologyMap ((functor F).map a.op) n

theorem map_comp {P Q T : ChainComplex C ℕ} (a : P ⟶ Q) (b : Q ⟶ T) (n : ℕ) :
    HomNaturality.map F (a ≫ b) n = HomNaturality.map F b n ≫ HomNaturality.map F a n := by
  simp only [HomNaturality.map, op_comp, (functor F).map_comp, HomologicalComplex.homologyMap_comp]

theorem map_eq_of_homotopy {P Q : ChainComplex C ℕ} {a b : P ⟶ Q}
    (h : Homotopy a b) (n : ℕ) : HomNaturality.map F a n = HomNaturality.map F b n :=
  (F.mapHomotopy h.op).homologyMap_eq n

theorem iso_hom {M : C} (P Q : ProjectiveResolution M) (n : ℕ) :
    (Hom.Comparison.homologyIso F P Q n).hom =
      HomNaturality.map F (ProjectiveResolution.lift (𝟙 M) Q P) n := rfl

theorem naturality {M N : C} (f : M ⟶ N)
    (P P' : ProjectiveResolution M) (Q Q' : ProjectiveResolution N)
    (a : P.complex ⟶ Q.complex) (b : P'.complex ⟶ Q'.complex)
    (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (hb : b ≫ Q'.π = P'.π ≫ (ChainComplex.single₀ C).map f) (n : ℕ) :
    HomNaturality.map F a n ≫ (Hom.Comparison.homologyIso F P P' n).hom =
      (Hom.Comparison.homologyIso F Q Q' n).hom ≫ HomNaturality.map F b n := by
  have hiP : ProjectiveResolution.lift (𝟙 M) P' P ≫ P.π = P'.π := by
    simp
  have hiQ : ProjectiveResolution.lift (𝟙 N) Q' Q ≫ Q.π = Q'.π := by
    simp
  have h : Homotopy (ProjectiveResolution.lift (𝟙 M) P' P ≫ a)
      (b ≫ ProjectiveResolution.lift (𝟙 N) Q' Q) :=
    ProjectiveResolution.liftHomotopy f _ _ (by
      rw [Category.assoc, ha, ← Category.assoc, hiP]) (by
      rw [Category.assoc, hiQ, hb])
  rw [iso_hom, iso_hom, ← HomNaturality.map_comp, ← HomNaturality.map_comp]
  exact map_eq_of_homotopy F h n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomNaturality
