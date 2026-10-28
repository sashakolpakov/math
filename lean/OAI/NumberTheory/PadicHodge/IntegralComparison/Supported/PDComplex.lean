import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopyNaturality

/-! # PD Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex

noncomputable section

/-! The actual supported Čech–PD complex of parameter principal opens
in an original affine crystalline frame. All arrows come from the
native principal-frame functor and original PD form presheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)
  (g : ℕ) (a : Fin g → Q.thickening.ring)

local notation "W" => WittVector p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring

def family : ULift.{u} (Fin g) → C := fun i => ⟨a i.down⟩

def restriction : ((AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W) ⥤
    (Cᵒᵖ ⥤ ModuleCat.{u} W) :=
  (Functor.whiskeringLeft _ _ _).obj (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).op

instance restriction_additive : (restriction p k X Q).Additive where
  map_add := rfl

def localizedComplex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} W) ℕ :=
  ((restriction p k X Q).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X)

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} W) (.up ℕ) (.up ℕ) :=
  AugmentedOrdered.CechFunctor.bicomplex (family p k X Q g a) (localizedComplex p k X Q)

def total : CochainComplex (ModuleCat.{u} W) ℕ := (bicomplex p k X Q g a).total (.up ℕ)

def topCoefficient : C := AugmentedOrdered.CechCoordinates.topObject (family p k X Q g a) g (by simp)

def topFrame : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (topCoefficient p k X Q g a)

def topProjection (i : Fin g) : topCoefficient p k X Q g a ⟶ family p k X Q g a ⟨i⟩ := by
  let e := monoEquivOfFin (ULift.{u} (Fin g)) (by simp : Fintype.card (ULift.{u} (Fin g)) = g)
  exact Pi.π (fun j : Fin g => family p k X Q g a (e j)) (e.symm ⟨i⟩) ≫
    eqToHom (congrArg (family p k X Q g a) (e.apply_symm_apply ⟨i⟩))

def coordinate (i : Fin g) : (topFrame p k X Q g a).thickening.ring :=
  (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (topCoefficient p k X Q g a)).ambientMap (a i)

theorem coordinate_isUnit (i : Fin g) : IsUnit (coordinate p k X Q g a i) :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.coefficient_unit p k X Q (topProjection p k X Q g a i)

def coordinateUnit (i : Fin g) : (topFrame p k X Q g a).thickening.ringˣ :=
  (coordinate_isUnit p k X Q g a i).unit

theorem coordinateUnit_val (i : Fin g) :
    (coordinateUnit p k X Q g a i : (topFrame p k X Q g a).thickening.ring) =
      coordinate p k X Q g a i := (coordinate_isUnit p k X Q g a i).unit_spec

theorem localizedComplex_d (q : ℕ) (r : C) :
    ((localizedComplex p k X Q).d q (q + 1)).app (op r) =
      ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential W (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r).thickening.ring
        (RingHom.ker (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r).thickening.reduction)
        (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r).thickening.dividedPowers q) := by
  have hd : (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X).d q (q + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.differentialPresheaf p k X q := by
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex]
    rw [CochainComplex.of_d]
  change ((restriction p k X Q).map
    ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X).d q (q + 1))).app (op r) = _
  rw [hd]
  rfl

def logarithmicForm : ((localizedComplex p k X Q).X g).obj (op (topCoefficient p k X Q g a)) :=
  PD.LogarithmicWedges.Forms.logarithmicWedge W (topFrame p k X Q g a).thickening.ring
    (RingHom.ker (topFrame p k X Q g a).thickening.reduction)
    (topFrame p k X Q g a).thickening.dividedPowers g (coordinateUnit p k X Q g a)

theorem logarithmicForm_closed :
    ((localizedComplex p k X Q).d g (g + 1)).app (op (topCoefficient p k X Q g a))
      (logarithmicForm p k X Q g a) = 0 := by
  rw [localizedComplex_d]
  exact PD.LogarithmicWedges.Forms.logarithmicWedge_closed _ _ _ _ g _

def residueCycle : Module.CochainClasses.cycles (PDComplex.total p k X Q g a) (g + g) :=
  AugmentedOrdered.CechTopTotal.topTotalCycle (family p k X Q g a) (localizedComplex p k X Q)
    g (by simp) g (logarithmicForm p k X Q g a) (logarithmicForm_closed p k X Q g a)

def residueClass : (PDComplex.total p k X Q g a).homology (g + g) :=
  Module.CochainClasses.classMap _ _ (residueCycle p k X Q g a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex
