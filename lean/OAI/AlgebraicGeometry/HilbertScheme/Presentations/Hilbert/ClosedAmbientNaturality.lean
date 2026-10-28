import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionIdealEmbedding

/-! # Closed Ambient Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientNaturality

noncomputable section

/-! The closed-ambient Hilbert map is natural for every test scheme
and is injective on native families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y)

theorem ambientEmbedding_naturality {T U : Over S} (a : T ⟶ U) :
    ClosedAmbientMap.ambientEmbedding j T ≫ Functor.ambientMap Y a = Functor.ambientMap X a ≫ ClosedAmbientMap.ambientEmbedding j U := by
  change (prod.map (𝟙 T) j).left ≫ (prod.map a (𝟙 Y)).left =
    (prod.map a (𝟙 X)).left ≫ (prod.map (𝟙 U) j).left
  rw [← Over.comp_left, ← Over.comp_left, prod.map_map, prod.map_map]
  simp only [Category.id_comp, Category.comp_id]

theorem ambientEmbedding_baseChange {T U : Over S} (a : T ⟶ U) :
    IsPullback (ClosedAmbientMap.ambientEmbedding j T) (Functor.ambientMap X a) (Functor.ambientMap Y a)
      (ClosedAmbientMap.ambientEmbedding j U) := by
  apply IsPullback.of_right _ (ambientEmbedding_naturality j a) (Functor.ambient_isPullback Y a)
  rw [ClosedAmbientMap.ambientEmbedding_projection, ClosedAmbientMap.ambientEmbedding_projection]
  exact Functor.ambient_isPullback X a

variable [IsClosedImmersion j.left]

theorem pushforwardFamily_baseChange {T U : Over S} (a : T ⟶ U) (F : Functor.Family X U) :
    ClosedAmbientMap.pushforwardFamily j (Functor.pullbackFamily X a F) = Functor.pullbackFamily Y a (ClosedAmbientMap.pushforwardFamily j F) := by
  apply Subtype.ext
  let h := (Functor.family_ambient_isPullback X a F.val).paste_horiz (ambientEmbedding_baseChange j a)
  change ((F.val.comap (Functor.ambientMap X a)).subschemeι ≫ ClosedAmbientMap.ambientEmbedding j T).ker =
    (F.val.subschemeι ≫ ClosedAmbientMap.ambientEmbedding j U).ker.comap (Functor.ambientMap Y a)
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

theorem pushforwardFamily_injective (T : Over S) : Function.Injective
    (ClosedAmbientMap.pushforwardFamily j : Functor.Family X T → Functor.Family Y T) := by
  intro F G h
  apply Subtype.ext
  exact Closed.ImmersionIdealEmbedding.ideal_map_closed_injective (ClosedAmbientMap.ambientEmbedding j T) (congrArg Subtype.val h)

def closedAmbientTransformation : Functor.familyFunctor X ⟶ Functor.familyFunctor Y where
  app _ := ↾fun F => ClosedAmbientMap.pushforwardFamily j F
  naturality T U a := by
    apply ConcreteCategory.hom_ext
    intro F
    exact pushforwardFamily_baseChange j a.unop F

instance closedAmbientTransformation_mono : Mono (closedAmbientTransformation j) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  exact (CategoryTheory.mono_iff_injective _).mpr (pushforwardFamily_injective j T.unop)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientNaturality
