import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

/-! # Determinant Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DeterminantTransition

noncomputable section

/-! The normalized top cohomology of the actual Koszul dual transforms by
exactly the determinant of the change of equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

section General
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (a : K ⟶ L) (n : ι) (hK : IsZero (K.X (c.next n))) (hL : IsZero (L.X (c.next n)))

open OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

@[reassoc]
theorem cycleClass_naturality : TopHomologyCokernel.cycleClass K n hK ≫ homologyMap a n =
    a.f n ≫ TopHomologyCokernel.cycleClass L n hL := by
  apply (cancel_mono (TopHomologyCokernel.iso L n hL).hom).mp
  rw [Category.assoc, TopHomologyCokernel.naturality a n hK hL,
    ← Category.assoc, TopHomologyCokernel.cycleClass_iso,
    cokernel.π_desc, Category.assoc, TopHomologyCokernel.cycleClass_iso]

end General

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix

variable (R : Type u) [CommRing R] {n : ℕ} (I : Ideal R)
  (s t : Fin n → R) (hs : OrientedTopCohomology.ideal R s = I) (ht : OrientedTopCohomology.ideal R t = I)
  (A : Matrix (Fin n) (Fin n) R) (hA : ∀ i, s i = ∑ j, A i j * t j)

def isoToIdeal (s : Fin n → R) (hs : OrientedTopCohomology.ideal R s = I) :
    (OrientedTopCohomology.dualComplex R s).homology n ≅ ModuleCat.of R (R ⧸ I) :=
  OrientedTopCohomology.iso R s ≪≫
    (Submodule.quotEquivOfEq _ _ hs).toModuleIso

@[reassoc]
theorem cycleClass_isoToIdeal :
    TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) n (OrientedTopCohomology.outgoing_isZero R s) ≫
      (isoToIdeal R I s hs).hom =
        ModuleCat.ofHom (I.mkQ.comp (OrientedTopCohomology.evaluation R s).toLinearMap) := by
  rw [isoToIdeal, Iso.trans_hom, ← Category.assoc, OrientedTopCohomology.cycleClass_iso]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

def dualChange : OrientedTopCohomology.dualComplex R t ⟶ OrientedTopCohomology.dualComplex R s :=
  DualComplexHomology.map R (GeneratorMatrix.change R s t A hA)

theorem dualChange_top (a : (OrientedTopCohomology.dualComplex R t).X n) :
    (dualChange R s t A hA).f n a = A.det • a :=
  GeneratorMatrix.dual_top R s t A hA a

theorem homology_transition :
    homologyMap (dualChange R s t A hA) n ≫ (isoToIdeal R I s hs).hom =
      (isoToIdeal R I t ht).hom ≫
        ModuleCat.ofHom (A.det • (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) := by
  let c := TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R t) n (OrientedTopCohomology.outgoing_isZero R t)
  let : Epi c := by
    dsimp [c, TopHomologyCokernel.cycleClass, TopHomologyCokernel.shortClass]
    infer_instance
  apply (cancel_epi c).mp
  dsimp only [c]
  rw [← Category.assoc, cycleClass_naturality (dualChange R s t A hA) n
    (OrientedTopCohomology.outgoing_isZero R t) (OrientedTopCohomology.outgoing_isZero R s), Category.assoc, cycleClass_isoToIdeal,
    ← Category.assoc, cycleClass_isoToIdeal]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change I.mkQ (OrientedTopCohomology.evaluation R s ((dualChange R s t A hA).f n a)) =
    A.det • I.mkQ (OrientedTopCohomology.evaluation R t a)
  rw [dualChange_top]
  exact (I.mkQ.map_smul A.det (OrientedTopCohomology.evaluation R t a)).trans rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DeterminantTransition
