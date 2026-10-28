import OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotient

/-! # Two Step Quotient Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotientNaturality

noncomputable section

/-! Actual morphisms of both quotient sequences induced by a morphism of the initial short complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {S T : ShortComplex C}

def firstQuotientMap (φ : S ⟶ T) : cokernel S.f ⟶ cokernel T.f :=
  cokernel.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

theorem firstQuotientMap_comp (φ : S ⟶ T) :
    cokernel.π S.f ≫ firstQuotientMap φ = φ.τ₂ ≫ cokernel.π T.f :=
  cokernel.π_desc _ _ _

theorem firstQuotientMap_differential (φ : S ⟶ T) :
    firstQuotientMap φ ≫ TwoStepQuotient.firstQuotientDifferential T = TwoStepQuotient.firstQuotientDifferential S ≫ φ.τ₃ :=
  cokernel.map_desc S.f S.g S.zero T.f T.g T.zero φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

def firstQuotientSequenceMap (φ : S ⟶ T) : TwoStepQuotient.firstQuotientSequence S ⟶ TwoStepQuotient.firstQuotientSequence T where
  τ₁ := φ.τ₁
  τ₂ := φ.τ₂
  τ₃ := firstQuotientMap φ
  comm₁₂ := φ.comm₁₂
  comm₂₃ := (firstQuotientMap_comp φ).symm

def secondQuotientMap (φ : S ⟶ T) :
    cokernel (TwoStepQuotient.firstQuotientDifferential S) ⟶ cokernel (TwoStepQuotient.firstQuotientDifferential T) :=
  cokernel.map (TwoStepQuotient.firstQuotientDifferential S) (TwoStepQuotient.firstQuotientDifferential T)
    (firstQuotientMap φ) φ.τ₃ (firstQuotientMap_differential φ).symm

theorem secondQuotientMap_comp (φ : S ⟶ T) :
    cokernel.π (TwoStepQuotient.firstQuotientDifferential S) ≫ secondQuotientMap φ =
      φ.τ₃ ≫ cokernel.π (TwoStepQuotient.firstQuotientDifferential T) := cokernel.π_desc _ _ _

def secondQuotientSequenceMap (φ : S ⟶ T) : TwoStepQuotient.secondQuotientSequence S ⟶ TwoStepQuotient.secondQuotientSequence T where
  τ₁ := firstQuotientMap φ
  τ₂ := φ.τ₃
  τ₃ := secondQuotientMap φ
  comm₁₂ := firstQuotientMap_differential φ
  comm₂₃ := (secondQuotientMap_comp φ).symm

theorem secondQuotientMap_differential (φ : S ⟶ T) {B B' : C}
    (d : S.X₃ ⟶ B) (hd : S.g ≫ d = 0) (d' : T.X₃ ⟶ B') (hd' : T.g ≫ d' = 0)
    (f : B ⟶ B') (hf : d ≫ f = φ.τ₃ ≫ d') :
    secondQuotientMap φ ≫ TwoStepQuotient.secondQuotientDifferential T d' hd' =
      TwoStepQuotient.secondQuotientDifferential S d hd ≫ f :=
  cokernel.map_desc (TwoStepQuotient.firstQuotientDifferential S) d (TwoStepQuotient.firstQuotientDifferential_next S d hd)
    (TwoStepQuotient.firstQuotientDifferential T) d' (TwoStepQuotient.firstQuotientDifferential_next T d' hd')
    (firstQuotientMap φ) φ.τ₃ f (firstQuotientMap_differential φ).symm hf

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotientNaturality
