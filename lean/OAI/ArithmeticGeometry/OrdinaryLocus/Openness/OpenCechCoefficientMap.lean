import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleCechNaturality

/-! # Open Cech Coefficient Map -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCoefficientMap.Construction

noncomputable section

/-! Actual maps of Cech short complexes induced by module-sheaf morphisms. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    {F G : TopCat.Sheaf (ModuleCat.{v} R) X} (φ : F ⟶ G) {ι : Type v} (U : ι → Opens X)

def openCechCoefficientMap0 : OpenCechDegreeZero.Construction.openModuleCechC0 F U →ₗ[R] OpenCechDegreeZero.Construction.openModuleCechC0 G U where
  toFun z i := φ.hom.app (op (U i)) (z i)
  map_add' x y := by funext i; exact map_add (φ.hom.app _).hom _ _
  map_smul' r x := by funext i; exact map_smul (φ.hom.app _).hom _ _

def openCechCoefficientMap1 : OpenCechDegreeZero.Construction.openModuleCechC1 F U →ₗ[R] OpenCechDegreeZero.Construction.openModuleCechC1 G U where
  toFun z i j := φ.hom.app (op (U i ⊓ U j)) (z i j)
  map_add' x y := by funext i j; exact map_add (φ.hom.app _).hom _ _
  map_smul' r x := by funext i j; exact map_smul (φ.hom.app _).hom _ _

def openCechCoefficientMap2 : OpenCechShortComplex.Construction.openModuleCechC2 F U →ₗ[R] OpenCechShortComplex.Construction.openModuleCechC2 G U where
  toFun z i j k := φ.hom.app (op ((U i ⊓ U j) ⊓ U k)) (z i j k)
  map_add' x y := by funext i j k; exact map_add (φ.hom.app _).hom _ _
  map_smul' r x := by funext i j k; exact map_smul (φ.hom.app _).hom _ _

theorem openCechRestrict1_naturality (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι)
    (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    φ.hom.app (op W) (OpenCechCocycles.Construction.openCechRestrict1 F U z i j W hi hj) =
      OpenCechCocycles.Construction.openCechRestrict1 G U (openCechCoefficientMap1 φ U z) i j W hi hj :=
  NatTrans.naturality_apply φ.hom (homOfLE (le_inf hi hj)).op (z i j)

theorem openCechCoefficientMap_d1 (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) :
    openCechCoefficientMap2 φ U (OpenCechShortComplex.Construction.openModuleCechD1 F U z) =
      OpenCechShortComplex.Construction.openModuleCechD1 G U (openCechCoefficientMap1 φ U z) := by
  funext i j k
  change φ.hom.app (op ((U i ⊓ U j) ⊓ U k))
    (OpenCechCocycles.Construction.openCechRestrict1 F U z i j _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
      OpenCechCocycles.Construction.openCechRestrict1 F U z j k _ (inf_le_left.trans inf_le_right) inf_le_right -
      OpenCechCocycles.Construction.openCechRestrict1 F U z i k _ (inf_le_left.trans inf_le_left) inf_le_right) = _
  rw [map_sub, map_add, openCechRestrict1_naturality, openCechRestrict1_naturality,
    openCechRestrict1_naturality]
  rfl

def openCechCoefficientMap : OpenCechShortComplex.Construction.openModuleCechShortComplex F U ⟶ OpenCechShortComplex.Construction.openModuleCechShortComplex G U where
  τ₁ := ModuleCat.ofHom (openCechCoefficientMap0 φ U)
  τ₂ := ModuleCat.ofHom (openCechCoefficientMap1 φ U)
  τ₃ := ModuleCat.ofHom (openCechCoefficientMap2 φ U)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i j
    exact (ModuleCechNaturality.Construction.openModuleCechD0_naturality F G φ U z i j).symm
  comm₂₃ := by
    ext z
    exact (openCechCoefficientMap_d1 φ U z).symm

def openModuleCechShortComplexFunctor (R : Type u) [CommRing R] (X : TopCat.{v})
    {ι : Type v} (U : ι → Opens X) :
    TopCat.Sheaf (ModuleCat.{v} R) X ⥤ ShortComplex (ModuleCat.{v} R) where
  obj F := OpenCechShortComplex.Construction.openModuleCechShortComplex F U
  map φ := openCechCoefficientMap φ U
  map_id F := by
    apply ShortComplex.Hom.ext <;> rfl
  map_comp φ ψ := by
    apply ShortComplex.Hom.ext <;> rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCoefficientMap.Construction
