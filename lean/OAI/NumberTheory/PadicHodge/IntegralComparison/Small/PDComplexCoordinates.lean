import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAlgebraCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # PD Complex Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates

noncomputable section

/-! The original small-site divided-power forms and their big-site
presentation are the same complex with canonically equal algebra actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "W" => WittVector p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X

def originalFunctor : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} W) ℕ where
  obj Q := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W Q.unop.thickening.ring
    (RingHom.ker Q.unop.thickening.reduction) Q.unop.thickening.dividedPowers
  map a := PD.DeRhamComplexMap.map (CommAlgCat.ofHom a.unop.ambientMap) a.unop.dp_comp
  map_id Q := PD.DeRhamComplexMap.map_id (𝟙 Q).unop.dp_comp
  map_comp a b := PD.DeRhamComplexMap.map_comp
    (CommAlgCat.ofHom a.unop.ambientMap) (CommAlgCat.ofHom b.unop.ambientMap)
    a.unop.dp_comp b.unop.dp_comp (a ≫ b).unop.dp_comp

def targetFunctor : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} W) ℕ :=
  (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65 ⋙ BigCrystallineSite.fromSmall).op ⋙
    GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X)

def pointIso (Q : Cᵒᵖ) : (originalFunctor p k X).obj Q ≅ (targetFunctor p k X).obj Q :=
  PD.DeRhamAlgebraCoordinates.iso W Q.unop.thickening.ring
    (RingHom.ker Q.unop.thickening.reduction) Q.unop.thickening.dividedPowers
    inferInstance (algebraMap W Q.unop.thickening.ring).toAlgebra toAlgebra_algebraMap.symm

theorem naturality {P Q : Cᵒᵖ} (a : P ⟶ Q) :
    (originalFunctor p k X).map a ≫ (pointIso p k X Q).hom =
      (pointIso p k X P).hom ≫ (targetFunctor p k X).map a :=
  PD.DeRhamAlgebraCoordinates.naturality W P.unop.thickening.ring
    (RingHom.ker P.unop.thickening.reduction) P.unop.thickening.dividedPowers
    Q.unop.thickening.ring (RingHom.ker Q.unop.thickening.reduction) Q.unop.thickening.dividedPowers
    inferInstance (algebraMap W P.unop.thickening.ring).toAlgebra
    inferInstance (algebraMap W Q.unop.thickening.ring).toAlgebra
    toAlgebra_algebraMap.symm toAlgebra_algebraMap.symm a.unop.ambientMap.toRingHom
    a.unop.ambientMap.commutes a.unop.ambientMap.commutes a.unop.dp_comp

def iso : originalFunctor p k X ≅ targetFunctor p k X :=
  NatIso.ofComponents (pointIso p k X) (naturality p k X)

def originalAssemblyIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (originalFunctor p k X) ≅
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simp only [Iso.refl_hom]
    apply NatTrans.ext
    funext Q
    change ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X).d i (i + 1)).app Q =
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W Q.unop.thickening.ring
        (RingHom.ker Q.unop.thickening.reduction) Q.unop.thickening.dividedPowers).d i (i + 1)
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    rfl)

def assembledIso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X ≅
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (targetFunctor p k X) :=
  (originalAssemblyIso p k X).symm ≪≫ (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso (iso p k X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates
