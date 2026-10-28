import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.TotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareSplit

/-! # Open Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal

noncomputable section

/-! Canonical global sections followed by a genuine restriction functor
commute with the original Čech total map, before any cohomology is taken. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r s
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D : Type r} [Category.{s} D]
  (F : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max w z} R) [F.Additive]
  (G : Sheaf J (ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max w z} R) [G.Additive]
  (e : Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0 ⟶ F)
  (b : F ⋙ Functor.const Dᵒᵖ ⟶ G)

local notation "S" => constantSheaf J (ModuleCat R)
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections.constantUnit R J) 0
local notation "V" => Functor.const Dᵒᵖ

local instance constantOpenWeakSheafify : HasWeakSheafify J (ModuleCat.{w} R) :=
  HasSheafify.isRightAdjoint

local instance constZero : (Functor.const Dᵒᵖ : ModuleCat.{max w z} R ⥤
    Dᵒᵖ ⥤ ModuleCat.{max w z} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def unit : ModuleCat.uliftFunctor.{z,w} R ⋙ V ⟶ S ⋙ G :=
  Functor.whiskerRight (TotalNaturality.unit R J) V ≫
    Functor.whiskerLeft S (Functor.whiskerRight e V ≫ b)

def sectionMap (M : CochainComplex (ModuleCat.{w} R) ℕ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
    (a : ((S).mapHomologicalComplex (.up ℕ)).obj M ⟶ K) :=
  ((V).mapHomologicalComplex (.up ℕ)).map
    (ComplexMap.map R J M K a ≫
      (e.mapHomologicalComplex (.up ℕ)).app K) ≫
        (b.mapHomologicalComplex (.up ℕ)).app K

theorem section_eq (M : CochainComplex (ModuleCat.{w} R) ℕ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
    (a : ((S).mapHomologicalComplex (.up ℕ)).obj M ⟶ K) :
    sectionMap R J F G e b M K a =
      ((unit R J F G e b).mapHomologicalComplex (.up ℕ)).app M ≫
        (G.mapHomologicalComplex (.up ℕ)).map a := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext W
  have hn := congrArg (fun q => q.app W) ((Functor.whiskerRight e V ≫ b).naturality (a.f i))
  change ((TotalNaturality.unit R J).app (M.X i) ≫
    (E).map (a.f i) ≫ e.app (K.X i)) ≫ (b.app (K.X i)).app W = _
  simp only [Category.assoc]
  exact congrArg (fun q => (TotalNaturality.unit R J).app (M.X i) ≫ q) hn

variable (Q : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{w} R) ℕ)
  (P : Dᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : Q ⋙ (constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ) ⟶ P)

def transformation : Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ) ⋙
    (V).mapHomologicalComplex (.up ℕ) ⟶ P ⋙ G.mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight
    (GeometricComparison.ConstantExt.ConstantExtSectionTransformation.transformation R J Q P a ≫
      Functor.whiskerLeft P (e.mapHomologicalComplex (.up ℕ)))
    ((V).mapHomologicalComplex (.up ℕ)) ≫
      Functor.whiskerLeft P (b.mapHomologicalComplex (.up ℕ))

theorem diagram : GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMap S
    (ModuleCat.uliftFunctor.{z,w} R ⋙ V) G Q P a (unit R J F G e b) =
      transformation R J F G e b Q P a := by
  apply NatTrans.ext
  funext W
  exact (section_eq R J F G e b (Q.obj W) (P.obj W) (a.app W)).symm

variable [HasBinaryProducts D]
  [HasProducts.{0} (Sheaf J (ModuleCat.{w} R))]
  [HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R))]
  {ι : Type} [Finite ι] (U : ι → D)

theorem total : sectionMap R J F G e b
      (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) (GeometricComparison.CechCone.Total.CechConeTotal.total U P)
      (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map S U Q P a) ≫
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).hom =
  ((V).mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (ModuleCat.uliftFunctor.{z,w} R) U Q).hom ≫
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map V U
      (Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ))
      (P ⋙ G.mapHomologicalComplex (.up ℕ)) (transformation R J F G e b Q P a) := CechCoefficient.SquareSplit.natural S
  (ModuleCat.uliftFunctor.{z,w} R) V G U Q P a (unit R J F G e b)
  (sectionMap R J F G e b
    (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) (GeometricComparison.CechCone.Total.CechConeTotal.total U P)
    (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map S U Q P a))
  (transformation R J F G e b Q P a)
  (section_eq R J F G e b _ _ (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map S U Q P a))
  (diagram R J F G e b Q P a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal
