import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame

/-! # Frame Chart Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameChartMap

noncomputable section

/-!
# IntegralComparison: chart algebra maps give actual morphisms between the original level-zero frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (k C D : Type u) [Field k] [CommRing C] [CommRing D]
  [Algebra k C] [Algebra k D] (f : C →ₐ[k] D)

def schemeMap : (Crystalline.Presentation.affineScheme k D).left ⟶ (Crystalline.Presentation.affineScheme k C).left :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

theorem schemeMap_over : schemeMap k C D f ≫ (Crystalline.Presentation.affineScheme k C).hom = (Crystalline.Presentation.affineScheme k D).hom := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k C)) =
    Spec.map (CommRingCat.ofHom (algebraMap k D))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext f.commutes

theorem quotientSquare :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (⊥ : Ideal D) f.toRingHom (by simp))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal D))) ≫ schemeMap k C D f := by
  change Spec.map (CommRingCat.ofHom (Ideal.quotientMap (⊥ : Ideal D) f.toRingHom _)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal D))) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun _ => rfl)

variable (p : ℕ) [Fact p.Prime] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  (jC : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) (jD : (Crystalline.Presentation.affineScheme k D).left ⟶ X.left)
  (hC : jC ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom) (hD : jD ≫ X.hom = (Crystalline.Presentation.affineScheme k D).hom)
  (h : schemeMap k C D f ≫ jC = jD)

def map : ZeroLevel.OpenFrame.frame p k D X jD hD ⟶ ZeroLevel.OpenFrame.frame p k C X jC hC where
  ringMap := IdealPDMap.map (dividedPowersBot D) f.toRingHom
  overBase := RingHom.ext (fun w => f.commutes (WittVector.constantCoeff w))
  overX := by
    change Spec.map (CommRingCat.ofHom (Ideal.quotientMap (⊥ : Ideal D) f.toRingHom _)) ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C))) ≫ jC) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal D))) ≫ jD
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ jC) (quotientSquare k C D f)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal D))) ≫ t) h)))

def boundedMap : ZeroLevel.OpenFrame.boundedFrame p k D X jD hD ⟶
    ZeroLevel.OpenFrame.boundedFrame p k C X jC hC :=
  ObjectProperty.homMk (FrameChartMap.map k C D f p X jC jD hC hD h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameChartMap
