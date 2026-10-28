import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Fiber Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberMap

noncomputable section

/-! Actual maps of the original geometric fibers and their compatibility with the original scalar automorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  (g : X ⟶ Y) (hg : g ≫ fY = fX)

def map : Frobenius.Geometry.geometricFiber (L := L) fX ⟶ Frobenius.Geometry.geometricFiber (L := L) fY :=
  pullback.lift (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ g)
    (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    ((Category.assoc _ _ _).trans ((congrArg (fun h => pullback.fst fX _ ≫ h) hg).trans pullback.condition))

theorem fst : FiberMap.map k L fX fY g hg ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
    pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ g := pullback.lift_fst _ _ _

theorem snd : FiberMap.map k L fX fY g hg ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
    pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) := pullback.lift_snd _ _ _

theorem isPullback : IsPullback (FiberMap.map k L fX fY g hg)
    (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))) g := by
  refine .of_right (t := (IsPullback.of_hasPullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))).flip) ?_ ?_
  · rw [FiberMap.snd, hg]
    exact (IsPullback.of_hasPullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).flip
  · exact FiberMap.fst k L fX fY g hg

theorem proper [IsProper g] : IsProper (FiberMap.map k L fX fY g hg) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback k L fX fY g hg).flip inferInstance

theorem geometricallyConnected [GeometricallyConnected g] : GeometricallyConnected (FiberMap.map k L fX fY g hg) :=
  MorphismProperty.of_isPullback (P := @GeometricallyConnected) (isPullback k L fX fY g hg).flip inferInstance

theorem scalar_natural (σ : L ≃ₐ[k] L) :
    FiberMap.map k L fX fY g hg ≫ (Frobenius.Geometry.geometricFiberIso fY σ).hom =
      (Frobenius.Geometry.geometricFiberIso fX σ).hom ≫ FiberMap.map k L fX fY g hg := by
  apply pullback.hom_ext
  · rw [Category.assoc, Frobenius.Geometry.geometricFiberIso_hom_fst, Category.assoc, FiberMap.fst,
      ← Category.assoc, Frobenius.Geometry.geometricFiberIso_hom_fst]
  · rw [Category.assoc, Frobenius.Geometry.geometricFiberIso_hom_snd, ← Category.assoc, FiberMap.snd,
      Category.assoc, FiberMap.snd, Frobenius.Geometry.geometricFiberIso_hom_snd]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberMap
