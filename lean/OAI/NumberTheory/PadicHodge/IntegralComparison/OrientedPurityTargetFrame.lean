import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomOrientedPurity
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Oriented Purity Target Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityTargetFrame

noncomputable section

/-! Changing the target-line trivialization scales the normalized purity
by the actual scalar change of frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

section Homology
variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c}

theorem homologyMap_smul (r : R) (f : K ⟶ L) (i : ι) :
    homologyMap (r • f) i = r • homologyMap f i := by
  change ShortComplex.homologyMap (r • (shortComplexFunctor (ModuleCat R) c i).map f) = _
  exact ShortComplex.homologyMap_smul _ _

end Homology

variable (P : ChainComplex (ModuleCat.{u} R) ℕ) (N : ModuleCat.{u} R)
  (e e' : N ≅ ModuleCat.of R R)

def toDual :
    ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op) ⟶ DualComplexHomology.complex R P :=
  ((NatIso.mapHomologicalComplex ((linearYoneda R (ModuleCat R)).mapIso e)
    (ComplexShape.down ℕ).symm).app P.op).hom ≫ (LinearHomDualPurity.complexIso R P).hom

theorem toDual_apply (m : ℕ) (a : P.X m ⟶ N) :
    ((toDual R P N e).f m).hom a = e.hom.hom.comp a.hom := rfl

theorem toDual_scale (r : R) (h : e'.hom = r • e.hom) :
    toDual R P N e' = r • toDual R P N e := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change P.X m ⟶ N at a
  apply LinearMap.ext
  intro x
  change e'.hom (a x) = r • e.hom (a x)
  exact congrArg (fun f : N ⟶ ModuleCat.of R R => f (a x)) h

theorem targetHomologyIso_hom (m : ℕ) :
    (LinearHomDualPurity.targetHomologyIso R P N e m).hom =
      homologyMap (toDual R P N e) m := by
  rw [toDual, homologyMap_comp]
  rfl

theorem targetHomologyIso_scale (r : R) (h : e'.hom = r • e.hom) (m : ℕ) :
    (LinearHomDualPurity.targetHomologyIso R P N e' m).hom =
      r • (LinearHomDualPurity.targetHomologyIso R P N e m).hom := by
  rw [targetHomologyIso_hom, targetHomologyIso_hom, toDual_scale R P N e e' r h,
    OrientedPurityTargetFrame.homologyMap_smul]

theorem frame_scalar : e'.hom = e'.hom (e.inv 1) • e.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : e.inv (e.hom x) = x := by
    exact congrArg (fun f : N ⟶ N => f x) e.hom_inv_id
  calc
    e'.hom x = e'.hom (e.inv (e.hom x)) := congrArg e'.hom hx.symm
    _ = e'.hom ((e.hom x) • e.inv 1) := by rw [← e.inv.hom.map_smul]; simp
    _ = (e.hom x) * e'.hom (e.inv 1) := e'.hom.hom.map_smul _ _
    _ = e'.hom (e.inv 1) • e.hom x := mul_comm _ _

variable {n : ℕ} (I : Ideal R) (s : Fin n → R)
  (hs : Koszul.OrientedTopCohomology.ideal R s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))

theorem purity_scale (r : R) (h : e'.hom = r • e.hom) :
    (LinearHomOrientedPurity.iso R I s hs hreg Q N e').hom =
      (LinearHomOrientedPurity.iso R I s hs hreg Q N e).hom ≫
        ModuleCat.ofHom (r • (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) := by
  dsimp only [LinearHomOrientedPurity.iso, Iso.trans_hom]
  rw [targetHomologyIso_scale R Q.complex N e e' r h, Linear.smul_comp]
  rw [show ModuleCat.ofHom (r • (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) =
    r • 𝟙 (ModuleCat.of R (R ⧸ I)) from rfl, Linear.comp_smul, Category.comp_id]

theorem purity_frame :
    (LinearHomOrientedPurity.iso R I s hs hreg Q N e').hom =
      (LinearHomOrientedPurity.iso R I s hs hreg Q N e).hom ≫
        ModuleCat.ofHom (e'.hom (e.inv 1) •
          (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) :=
  purity_scale R N e e' I s hs hreg Q _ (frame_scalar R N e e')

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityTargetFrame
