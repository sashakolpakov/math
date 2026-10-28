import OAI.RepresentationTheory.Theta.Geometric.Affine.BaseChangeCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Affine.Dominance
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Parameter Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.ParameterBaseChange

noncomputable section

/-! Native parameter changes of an arbitrary flat family. Injected
parameter algebras give faithful line-bundle pullback without a
flatness assumption on the parameter inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S]

theorem algebraSpecMap_comp (f : S →ₐ[A] R) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A S)) =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom f.comp_algebraMap

abbrev parameterBaseChange {Y : Scheme} (h : Y ⟶ Spec (.of A)) (R : Type)
    [CommRing R] [Algebra A R] : Scheme :=
  pullback h (Spec.map (CommRingCat.ofHom (algebraMap A R)))

def parameterBaseChangeMap {Y : Scheme} (h : Y ⟶ Spec (.of A)) (f : S →ₐ[A] R) :
    parameterBaseChange h R ⟶ parameterBaseChange h S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
    (by rw [Category.assoc, algebraSpecMap_comp]; exact pullback.condition)

theorem parameterBaseChangeMap_fst {Y : Scheme} (h : Y ⟶ Spec (.of A)) (f : S →ₐ[A] R) :
    parameterBaseChangeMap h f ≫ pullback.fst _ _ =
      pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  exact pullback.lift_fst _ _ _

theorem parameterBaseChangeMap_snd {Y : Scheme} (h : Y ⟶ Spec (.of A)) (f : S →ₐ[A] R) :
    parameterBaseChangeMap h f ≫ pullback.snd _ _ =
      pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap A R))) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  exact pullback.lift_snd _ _ _

theorem parameterBaseChangeMap_isPullback {Y : Scheme} (h : Y ⟶ Spec (.of A)) (f : S →ₐ[A] R) :
    IsPullback (parameterBaseChangeMap h f)
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap A R))))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap A S))))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  apply IsPullback.of_right _ (parameterBaseChangeMap_snd h f)
    (IsPullback.of_hasPullback h (Spec.map (CommRingCat.ofHom (algebraMap A S))))
  rw [parameterBaseChangeMap_fst, algebraSpecMap_comp]
  exact IsPullback.of_hasPullback _ _

theorem parameterBaseChangeMap_dominant {Y : Scheme} (h : Y ⟶ Spec (.of A)) [Flat h]
    (f : S →ₐ[A] R) (hf : Function.Injective f) : IsSchemeTheoreticallyDominant (parameterBaseChangeMap h f) := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    Affine.Dominance.specMap_schemeTheoreticallyDominant f.toRingHom hf
  exact IsSchemeTheoreticallyDominant.of_isPullback (parameterBaseChangeMap_isPullback h f).flip

theorem parameterBaseChangeMap_quasiCompact {Y : Scheme} (h : Y ⟶ Spec (.of A)) (f : S →ₐ[A] R) :
    QuasiCompact (parameterBaseChangeMap h f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (parameterBaseChangeMap_isPullback h f).flip
    (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f.toRingHom))))

end

end OAI.RepresentationTheory.Theta.Geometric.ParameterBaseChange
