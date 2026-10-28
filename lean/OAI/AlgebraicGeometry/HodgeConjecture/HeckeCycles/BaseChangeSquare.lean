import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Base Change Square -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel

/-! Build the local comparison model by base changing one abelian scheme
along a commuting square of actual base morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
  (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k)

def genericGroupIso :
    Grp.mk ((G.pullback t).pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).scheme ≅
      Grp.mk ((G.pullback k).pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme :=
  (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeCompGroupIso G (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])) t).symm ≪≫
    AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorGroupIso G (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) k
      (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t) w.symm

def genericIso :
    ((G.pullback t).pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).scheme ≅
      ((G.pullback k).pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme :=
  (Grp.forget _).mapIso (genericGroupIso G k t w)

omit [NumberField K] in
theorem genericIso_group : IsMonHom (ComparisonModel.genericIso G k t w).hom :=
  (genericGroupIso G k t w).hom.hom.isMonHom_hom

def model : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq where
  dimension := g
  variety := G.pullback k
  integral := G.pullback t
  genericIso := ComparisonModel.genericIso G k t w
  genericIso_group := ComparisonModel.genericIso_group G k t w

theorem model_variety : (model G k t w).variety.scheme = (G.pullback k).scheme := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

/-! The underlying maps of the actual group-valued base-change
comparisons are the canonical scheme comparisons, natural for every
scheme map, including Albanese maps whose source is not a group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence

variable {S T U : Scheme} (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S) (w : f ≫ h = x)

def factorIso (X : Over S) :
    (Over.pullback x).obj X ≅ (Over.pullback f).obj ((Over.pullback h).obj X) :=
  (eqToIso (congrArg (fun b => (Over.pullback b).obj X) w)).symm ≪≫
    (Over.pullbackComp f h).app X

theorem factorIso_naturality {X Y : Over S} (a : X ⟶ Y) :
    (Over.pullback x).map a ≫ (factorIso f h x w Y).hom =
      (factorIso f h x w X).hom ≫ (Over.pullback f).map ((Over.pullback h).map a) := by
  subst x
  change (Over.pullback (f ≫ h)).map a ≫ (𝟙 _ ≫ (Over.pullbackComp f h).hom.app Y) =
    (𝟙 _ ≫ (Over.pullbackComp f h).hom.app X) ≫ (Over.pullback f).map ((Over.pullback h).map a)
  simp only [Category.id_comp]
  exact (Over.pullbackComp f h).hom.naturality a

theorem factorIso_inv_naturality {X Y : Over S} (a : X ⟶ Y) :
    (Over.pullback f).map ((Over.pullback h).map a) ≫ (factorIso f h x w Y).inv =
      (factorIso f h x w X).inv ≫ (Over.pullback x).map a := by
  subst x
  change (Over.pullback f).map ((Over.pullback h).map a) ≫
    ((Over.pullbackComp f h).inv.app Y ≫ 𝟙 _) =
      ((Over.pullbackComp f h).inv.app X ≫ 𝟙 _) ≫ (Over.pullback (f ≫ h)).map a
  simp only [Category.comp_id]
  exact (Over.pullbackComp f h).inv.naturality a

theorem groupComp_hom {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    ((Grp.forget (Over U)).mapIso (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeCompGroupIso A f h)).hom =
      ((Over.pullbackComp f h).app A.scheme).hom := by
  change ((Over.pullbackComp f h).app A.scheme).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem groupFactor_hom {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A f h x w).hom = (factorIso f h x w A.scheme).hom := by
  subst x
  change (𝟙 _) ≫ (((Over.pullbackComp f h).app A.scheme).hom ≫ 𝟙 _) =
    (𝟙 _) ≫ ((Over.pullbackComp f h).app A.scheme).hom
  rw [Category.comp_id]

variable {V : Scheme} (d : V ⟶ T) (e : V ⟶ U) (b : T ⟶ S) (c : U ⟶ S)
  (commutes : d ≫ b = e ≫ c)

def squareIso (X : Over S) :
    (Over.pullback d).obj ((Over.pullback b).obj X) ≅
      (Over.pullback e).obj ((Over.pullback c).obj X) :=
  ((Over.pullbackComp d b).app X).symm ≪≫ factorIso e c (d ≫ b) commutes.symm X

theorem squareIso_naturality {X Y : Over S} (a : X ⟶ Y) :
    (Over.pullback d).map ((Over.pullback b).map a) ≫ (squareIso d e b c commutes Y).hom =
      (squareIso d e b c commutes X).hom ≫ (Over.pullback e).map ((Over.pullback c).map a) := by
  change (Over.pullback d).map ((Over.pullback b).map a) ≫
    ((Over.pullbackComp d b).app Y).inv ≫ (factorIso e c (d ≫ b) commutes.symm Y).hom = _
  have hn : (Over.pullback d).map ((Over.pullback b).map a) ≫
      ((Over.pullbackComp d b).app Y).inv =
    ((Over.pullbackComp d b).app X).inv ≫ (Over.pullback (d ≫ b)).map a :=
    (Over.pullbackComp d b).inv.naturality a
  rw [← Category.assoc, hn, Category.assoc,
    factorIso_naturality]
  rfl

theorem squareIso_comparisonModel
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
    (hw : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k) :
    (ComparisonModel.genericIso A k t hw).hom =
      (squareIso (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))
        (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k hw A.scheme).hom := by
  change ((Grp.forget _).mapIso
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeCompGroupIso A (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])) t)).inv ≫
      (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) k _ hw.symm).hom = _
  rw [groupFactor_hom]
  congr 1

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

end

end OAI
