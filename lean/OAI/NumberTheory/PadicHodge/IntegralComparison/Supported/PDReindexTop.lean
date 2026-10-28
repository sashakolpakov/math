import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDFrameIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop

/-! # PD Reindex Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDReindexTop

noncomputable section

/-! The canonical product identification carries the logarithmic
form in a transported principal frame to the literal target residue form. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X} (e : P ≅ Q)
  (g : ℕ) (a : Fin g → Q.thickening.ring)

local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Iso.coefficients p k X e
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.family p k X Q g a

local instance preserves : PreservesFiniteLimits r := by
  change PreservesFiniteLimits (Principal.CoefficientChange.functor e.hom.ambientMap.toRingHom)
  infer_instance

def parameters : Fin g → P.thickening.ring := fun i => e.hom.ambientMap (a i)

def topIso : (r).obj (PDComplex.topCoefficient p k X Q g a) ≅
    PDComplex.topCoefficient p k X P g (parameters p k X e g a) :=
  AugmentedOrdered.CechReindexTop.objectIso r U g (by simp)

def map : PDComplex.topFrame p k X P g (parameters p k X e g a) ⟶
    PDFrameIso.topFrame p k X e g a :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X P (topIso p k X e g a).inv

theorem map_coordinate (i : Fin g) :
    (PDReindexTop.map p k X e g a).ambientMap (PDFrameIso.coordinate p k X e g a i) =
      PDComplex.coordinate p k X P g (parameters p k X e g a) i :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_algebraMap p k X P (topIso p k X e g a).inv
    (e.hom.ambientMap (a i))

theorem map_unit (i : Fin g) :
    Units.map (PDReindexTop.map p k X e g a).ambientMap.toMonoidHom
      (PDFrameIso.coordinateUnit p k X e g a i) =
      PDComplex.coordinateUnit p k X P g (parameters p k X e g a) i := by
  apply Units.ext
  change (PDReindexTop.map p k X e g a).ambientMap
    (↑(PDFrameIso.coordinateUnit p k X e g a i) :
      (PDFrameIso.topFrame p k X e g a).thickening.ring) = _
  dsimp only [PDFrameIso.coordinateUnit]
  rw [(PDFrameIso.coordinate_isUnit p k X e g a i).unit_spec, map_coordinate]
  exact (PDComplex.coordinateUnit_val p k X P g (parameters p k X e g a) i).symm

theorem map_logarithmicForm :
    ((PDComplex.localizedComplex p k X P).X g).map (topIso p k X e g a).inv.op
      (PDFrameIso.logarithmicForm p k X e g a) =
      PDComplex.logarithmicForm p k X P g (parameters p k X e g a) := by
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (PDReindexTop.map p k X e g a).ambientMap)
    (PDReindexTop.map p k X e g a).dp_comp g
    (PD.LogarithmicWedges.Forms.logarithmicWedge _ _ _ _ g _) = _
  rw [PD.LogarithmicFrame.Forms.formMap_logarithmicWedge]
  exact congrArg (PD.LogarithmicWedges.Forms.logarithmicWedge (WittVector p k)
    (PDComplex.topFrame p k X P g (parameters p k X e g a)).thickening.ring
    (RingHom.ker (PDComplex.topFrame p k X P g (parameters p k X e g a)).thickening.reduction)
    (PDComplex.topFrame p k X P g (parameters p k X e g a)).thickening.dividedPowers g)
    (funext (map_unit p k X e g a))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDReindexTop
