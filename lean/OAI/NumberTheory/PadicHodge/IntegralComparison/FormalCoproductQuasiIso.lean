import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! # Formal Coproduct Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FormalCoproductQuasiIso

noncomputable section

/-! Evaluation on a genuine formal coproduct preserves quasi-isomorphisms
which are quasi-isomorphisms on all its summands. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t

variable (R : Type u) [CommRing R]

local instance limits : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max u v, u}

local instance exactLimits (ι : Type v) :
    HasExactLimitsOfShape (Discrete ι) (ModuleCat.{max u v} R) := by
  let : AB4StarOfSize.{v} AddCommGrpCat.{max u v} := AB4StarOfSize_shrink _
  exact HasExactLimitsOfShape.domain_of_functor (Discrete ι)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

abbrev product (ι : Type v) :
    (Discrete ι ⥤ ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R := lim

local instance constAdditive (ι : Type v) :
    (Functor.const (Discrete ι) : ModuleCat.{max u v} R ⥤
      Discrete ι ⥤ ModuleCat.{max u v} R).Additive where
  map_add := by intros; rfl

instance product_additive (ι : Type v) : (product R ι).Additive :=
  (constLimAdj (J := Discrete ι) (C := ModuleCat.{max u v} R)).right_adjoint_additive

instance product_preservesHomology (ι : Type v) : (product R ι).PreservesHomology := by
  dsimp only [product]
  infer_instance

theorem product_quasiIso (ι : Type v)
    {K L : CochainComplex (Discrete ι ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L)
    (hf : ∀ i : Discrete ι, QuasiIso
      ((((evaluation (Discrete ι) (ModuleCat.{max u v} R)).obj i).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso (((product R ι).mapHomologicalComplex (.up ℕ)).map f) := by
  let : QuasiIso f := (HomologicalComplex.quasiIso_iff_evaluation f).mpr hf
  infer_instance

variable {C : Type s} [Category.{t} C] (E : FormalCoproduct.{v} C)

def indices : Discrete E.I ⥤ Cᵒᵖ := Discrete.functor (fun i => op (E.obj i))

def evaluation : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R :=
  FormalCoproduct.evalOp C (ModuleCat.{max u v} R) ⋙
    (CategoryTheory.evaluation (FormalCoproduct.{v} C)ᵒᵖ (ModuleCat.{max u v} R)).obj (op E)

def productEvaluation : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R :=
  (Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (indices E) ⋙ product R E.I

def diagramIso (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    Discrete.functor (fun i => P.obj (op (E.obj i))) ≅ indices E ⋙ P :=
  Discrete.natIso (fun _ => Iso.refl _)

def componentIso (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    (FormalCoproductQuasiIso.evaluation R E).obj P ≅ (productEvaluation R E).obj P :=
  HasLimit.isoOfNatIso (diagramIso R E P)

theorem component_pi (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (i : Discrete E.I) :
    (componentIso R E P).hom ≫ limit.π (indices E ⋙ P) i =
      Limits.Pi.π (fun i => P.obj (op (E.obj i))) i.as :=
  (HasLimit.isoOfNatIso_hom_π (diagramIso R E P) i).trans (Category.comp_id _)

def evaluationIso : FormalCoproductQuasiIso.evaluation R E ≅ productEvaluation R E :=
  NatIso.ofComponents (fun P => componentIso R E P) (by
    intro F G f
    apply limit.hom_ext
    intro i
    change (Limits.Pi.map (fun i => f.app (op (E.obj i))) ≫
      (componentIso R E G).hom) ≫ limit.π (indices E ⋙ G) i =
      ((componentIso R E F).hom ≫
        lim.map (Functor.whiskerLeft (indices E) f)) ≫ limit.π (indices E ⋙ G) i
    let φ := Limits.Pi.map (fun i => f.app (op (E.obj i)))
    have hg := component_pi R E G i
    have hf := component_pi R E F i
    have hl := limMap_π (Functor.whiskerLeft (indices E) f) i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => φ ≫ t) hg).trans
        ((Limits.Pi.map_π _ i.as).trans
          ((congrArg (fun t => t ≫ f.app (op (E.obj i.as))) hf).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun t => (componentIso R E F).hom ≫ t) hl).symm.trans
                (Category.assoc _ _ _).symm))))))

instance evaluation_additive : (FormalCoproductQuasiIso.evaluation R E).Additive where
  map_add {F G} f g := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [FormalCoproductQuasiIso.evaluation, Functor.comp_map]
    change Limits.Pi.map (fun i => (f + g).app (op (E.obj i))) ≫ _ =
      (Limits.Pi.map (fun i => f.app (op (E.obj i))) +
        Limits.Pi.map (fun i => g.app (op (E.obj i)))) ≫ _
    simp [Preadditive.add_comp, Preadditive.comp_add]

instance productEvaluation_additive : (productEvaluation R E).Additive := by
  dsimp only [productEvaluation]
  infer_instance

theorem quasiIso {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (f : K ⟶ L)
    (hf : ∀ i : E.I, QuasiIso
      ((((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj
        (op (E.obj i))).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso (((FormalCoproductQuasiIso.evaluation R E).mapHomologicalComplex (.up ℕ)).map f) := by
  let F := (Functor.whiskeringLeft (Discrete E.I) Cᵒᵖ
    (ModuleCat.{max u v} R)).obj (indices E)
  let : QuasiIso (((productEvaluation R E).mapHomologicalComplex (.up ℕ)).map f) :=
    product_quasiIso R E.I ((F.mapHomologicalComplex (.up ℕ)).map f) (fun i => hf i.as)
  exact QuasiIsoFunctorIso.transport _ _
    (NatIso.mapHomologicalComplex (evaluationIso R E).symm (.up ℕ)) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FormalCoproductQuasiIso
