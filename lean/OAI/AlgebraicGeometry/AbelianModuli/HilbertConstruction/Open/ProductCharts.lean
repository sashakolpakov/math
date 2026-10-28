import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Product Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ProductCharts

noncomputable section

/-! Products of open chart maps and their exact images in a fiber product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y U V : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (a : U ⟶ X) (b : V ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]

def openProductChartMap : pullback (a ≫ f) (b ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ a b (𝟙 S) (Category.comp_id _) (Category.comp_id _)

instance openProductChartMap_isOpenImmersion : IsOpenImmersion (openProductChartMap f g a b) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

omit [IsOpenImmersion a] [IsOpenImmersion b] in
theorem openProductChartMap_fst :
    openProductChartMap f g a b ≫ pullback.fst f g = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _

omit [IsOpenImmersion a] [IsOpenImmersion b] in
theorem openProductChartMap_snd :
    openProductChartMap f g a b ≫ pullback.snd f g = pullback.snd _ _ ≫ b := pullback.lift_snd _ _ _

def openProductChartOpen : (pullback f g).Opens :=
  (pullback.fst f g ⁻¹ᵁ a.opensRange) ⊓ (pullback.snd f g ⁻¹ᵁ b.opensRange)

def openProductChartOpenLeft : (openProductChartOpen f g a b).toScheme ⟶ U :=
  IsOpenImmersion.lift a ((openProductChartOpen f g a b).ι ≫ pullback.fst f g) (by
    rintro _ ⟨x, rfl⟩
    exact x.property.1)

def openProductChartOpenRight : (openProductChartOpen f g a b).toScheme ⟶ V :=
  IsOpenImmersion.lift b ((openProductChartOpen f g a b).ι ≫ pullback.snd f g) (by
    rintro _ ⟨x, rfl⟩
    exact x.property.2)

theorem openProductChartOpenLeft_fac :
    openProductChartOpenLeft f g a b ≫ a = (openProductChartOpen f g a b).ι ≫ pullback.fst f g :=
  IsOpenImmersion.lift_fac _ _ _

theorem openProductChartOpenRight_fac :
    openProductChartOpenRight f g a b ≫ b = (openProductChartOpen f g a b).ι ≫ pullback.snd f g :=
  IsOpenImmersion.lift_fac _ _ _

def openProductChartOpenLift : (openProductChartOpen f g a b).toScheme ⟶ pullback (a ≫ f) (b ≫ g) :=
  pullback.lift (openProductChartOpenLeft f g a b) (openProductChartOpenRight f g a b) (by
    rw [← Category.assoc, openProductChartOpenLeft_fac, Category.assoc, pullback.condition,
      ← Category.assoc, ← openProductChartOpenRight_fac, Category.assoc])

theorem openProductChartOpenLift_fac :
    openProductChartOpenLift f g a b ≫ openProductChartMap f g a b = (openProductChartOpen f g a b).ι := by
  apply pullback.hom_ext
  · simp only [Category.assoc, openProductChartMap_fst, openProductChartOpenLift,
      pullback.lift_fst_assoc, openProductChartOpenLeft_fac]
  · simp only [Category.assoc, openProductChartMap_snd, openProductChartOpenLift,
      pullback.lift_snd_assoc, openProductChartOpenRight_fac]

theorem openProductChartMap_opensRange :
    (openProductChartMap f g a b).opensRange = openProductChartOpen f g a b := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · refine ⟨pullback.fst (a ≫ f) (b ≫ g) z, ?_⟩
      exact (congrArg (fun k : pullback (a ≫ f) (b ≫ g) ⟶ X => k z)
        (openProductChartMap_fst f g a b)).symm
    · refine ⟨pullback.snd (a ≫ f) (b ≫ g) z, ?_⟩
      exact (congrArg (fun k : pullback (a ≫ f) (b ≫ g) ⟶ Y => k z)
        (openProductChartMap_snd f g a b)).symm
  · intro hx
    refine ⟨openProductChartOpenLift f g a b ⟨x, hx⟩, ?_⟩
    exact congrArg (fun k : (openProductChartOpen f g a b).toScheme ⟶ pullback f g => k ⟨x, hx⟩)
      (openProductChartOpenLift_fac f g a b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ProductCharts
