import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent

/-! # Algebra Field Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlgebraFieldTest.CM

noncomputable section

/-! A field embedding over the Witt fraction field preserves the
canonical arithmetic test map. The corresponding change of test is
constructed with the actual field embedding as its underlying map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K L L' : Type} [Field K] [Field L] [Field L']
  [Algebra K L] [Algebra K L'] {S : Scheme}
  (b : Spec (.of K) ⟶ S) (σ : L →ₐ[K] L')

theorem base_eq : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b) =
      Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ b := by
  have h : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) = Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
    rw [← Spec.map_comp]
    exact congrArg (fun f : K →+* L' => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h)

def testIso : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ b) ≅
    Over.mk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b)) :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (base_eq b σ))

def map : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ b) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (base_eq b σ)

theorem map_eq : CM.map b σ = (testIso b σ).hom ≫
    FieldPointDescent.CM.testMap σ.toRingHom (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b) := by
  apply Over.OverMorphism.ext
  exact (Category.id_comp (Spec.map (CommRingCat.ofHom σ.toRingHom))).symm

instance map_epi : Epi (CM.map b σ) := by
  rw [map_eq]
  infer_instance

theorem source_square : CM.map b σ ≫ FieldPointDescent.CM.testMap (algebraMap K L) b =
    FieldPointDescent.CM.testMap (algebraMap K L') b := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : K →+* L' => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlgebraFieldTest.CM
