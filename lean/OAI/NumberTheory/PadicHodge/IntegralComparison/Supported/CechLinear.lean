import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLinear

/-! # Cech Linear -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLinear.HomotopyEquivalence

noncomputable section

/-! The actual supported Cech total cohomology preserves addition and
ambient scalars. These instances keep scalar residue detection on the
original total complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → C)

local instance totalExists (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

local instance totalAdditive :
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ) (.up ℕ)).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change K.ιTotal (.up ℕ) p q n hpq ≫
      (HomologicalComplex₂.total.map (f + g) (.up ℕ)).f n =
      K.ιTotal (.up ℕ) p q n hpq ≫
        ((HomologicalComplex₂.total.map f (.up ℕ)).f n +
          (HomologicalComplex₂.total.map g (.up ℕ)).f n)
    rw [Preadditive.comp_add, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map]
    rw [HomologicalComplex.add_f_apply, HomologicalComplex.add_f_apply,
      Preadditive.add_comp]

local instance totalLinear :
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ) (.up ℕ)).Linear R where
  map_smul {K L} f r := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change K.ιTotal (.up ℕ) p q n hpq ≫
      (HomologicalComplex₂.total.map (r • f) (.up ℕ)).f n =
      K.ιTotal (.up ℕ) p q n hpq ≫
        (r • (HomologicalComplex₂.total.map f (.up ℕ)).f n)
    rw [Linear.comp_smul, HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map]
    change (r • (f.f p).f q) ≫ L.ιTotal (.up ℕ) p q n hpq = _
    rw [Linear.smul_comp]

local instance homologyLinear (q : ℕ) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).Linear R where
  map_smul f r := Resolution.CohomologyMaps.homologyMap_smul R f r q

instance additive (q : ℕ) : (CechHomotopyEquivalence.functor (R := R) U q).Additive := by
  dsimp only [CechHomotopyEquivalence.functor]
  infer_instance

instance linear (q : ℕ) : (CechHomotopyEquivalence.functor (R := R) U q).Linear R := by
  dsimp only [CechHomotopyEquivalence.functor]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLinear.HomotopyEquivalence
