import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ConcentrationHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationZigzagSingle

/-! # Functor Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.FunctorConcentration

noncomputable section

/-! Original concentration maps remain normalized after an additive
functor preserving the homology of the three complexes involved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z u' v'
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

theorem exactAt (K : CochainComplex C ℕ) (q : ℕ)
    [F.PreservesLeftHomologyOf (K.sc q)] (hK : K.ExactAt q) :
    ((F.mapHomologicalComplex (.up ℕ)).obj K).ExactAt q := by
  apply (exactAt_iff_isZero_homology _ _).mpr
  exact (F.map_isZero ((exactAt_iff_isZero_homology _ _).mp hK)).of_iso
    ((K.sc q).mapHomologyIso F)

theorem quasiIso {K L : CochainComplex C ℕ}
    [∀ q, F.PreservesLeftHomologyOf (K.sc q)]
    [∀ q, F.PreservesLeftHomologyOf (L.sc q)] (a : K ⟶ L) [QuasiIso a] :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map a) := by
  constructor
  intro q
  let : ShortComplex.QuasiIso ((shortComplexFunctor C (.up ℕ) q).map a) :=
    (quasiIsoAt_iff a q).mp inferInstance
  rw [quasiIsoAt_iff]
  change ShortComplex.QuasiIso (F.mapShortComplex.map
    ((shortComplexFunctor C (.up ℕ) q).map a))
  infer_instance

variable (K : CochainComplex C ℕ) (c : ℕ)
  (hK : ∀ q, q ≠ c → K.ExactAt q)
  [∀ q, F.PreservesLeftHomologyOf (K.sc q)]
  [∀ q, F.PreservesLeftHomologyOf ((CohomologyConcentration.truncation K c).sc q)]
  [∀ q, F.PreservesLeftHomologyOf (((single C (.up ℕ) c).obj (K.homology c)).sc q)]
  {E : Type u'} [Category.{v'} E]
  (G : CochainComplex D ℕ ⥤ E)
  (hG : ∀ {P Q : CochainComplex D ℕ} (a : P ⟶ Q), QuasiIso a → IsIso (G.map a))
  [IsIso (((F.mapHomologicalComplex (.up ℕ)) ⋙ G).map (CohomologyConcentration.projection K c))]
  [IsIso (((F.mapHomologicalComplex (.up ℕ)) ⋙ G).map (CohomologyConcentration.inclusion K c))]

include hK hG in
theorem map_to_single (N : D)
    (a : ((F.mapHomologicalComplex (.up ℕ)).obj K) ⟶ (single D (.up ℕ) c).obj N) :
    G.map a =
      (Functor.ConcentrationSingle.iso ((F.mapHomologicalComplex (.up ℕ)) ⋙ G) K c).hom ≫
        G.map ((singleMapHomologicalComplex F (.up ℕ) c).hom.app (K.homology c)) ≫
          G.map ((single D (.up ℕ) c).map
            (((K.sc c).mapHomologyIso F).inv ≫ homologyMap a c ≫
              (singleObjHomologySelfIso (.up ℕ) c N).hom)) := by
  let FK := (F.mapHomologicalComplex (.up ℕ)).obj K
  let FS := (F.mapHomologicalComplex (.up ℕ)).obj
    ((single C (.up ℕ) c).obj (K.homology c))
  let FT := (F.mapHomologicalComplex (.up ℕ)).obj (CohomologyConcentration.truncation K c)
  let p := (F.mapHomologicalComplex (.up ℕ)).map (CohomologyConcentration.projection K c)
  let i := (F.mapHomologicalComplex (.up ℕ)).map (CohomologyConcentration.inclusion K c)
  let : QuasiIso (CohomologyConcentration.projection K c) := CohomologyConcentration.projection_quasiIso K c hK
  let : QuasiIso p := quasiIso F (CohomologyConcentration.projection K c)
  have hFK : ∀ q, q ≠ c → FK.ExactAt q := fun q hq => exactAt F K q (hK q hq)
  have hFS : ∀ q, q ≠ c → FS.ExactAt q := fun q hq => exactAt F _ q
    (exactAt_single_obj (.up ℕ) c (K.homology c) q hq)
  have hFT : ∀ q, q ≠ c → FT.ExactAt q := fun q hq => exactAt F _ q
    ((exactAt_iff_of_quasiIsoAt (CohomologyConcentration.projection K c) q).mp (hK q hq))
  let : IsIso (G.map i) := inferInstanceAs
    (IsIso (((F.mapHomologicalComplex (.up ℕ)) ⋙ G).map (CohomologyConcentration.inclusion K c)))
  let : IsIso (G.map (CohomologyConcentration.projection FK c)) := hG _ (CohomologyConcentration.projection_quasiIso FK c hFK)
  let : IsIso (G.map (CohomologyConcentration.inclusion FK c)) := hG _ (CohomologyConcentration.inclusion_quasiIso FK c hFK)
  let : IsIso (G.map (CohomologyConcentration.projection FS c)) := hG _ (CohomologyConcentration.projection_quasiIso FS c hFS)
  let : IsIso (G.map (CohomologyConcentration.inclusion FS c)) := hG _ (CohomologyConcentration.inclusion_quasiIso FS c hFS)
  let : IsIso (G.map (CohomologyConcentration.projection FT c)) := hG _ (CohomologyConcentration.projection_quasiIso FT c hFT)
  let : IsIso (G.map (CohomologyConcentration.inclusion FT c)) := hG _ (CohomologyConcentration.inclusion_quasiIso FT c hFT)
  let : IsIso (G.map (CohomologyConcentration.projection ((single D (.up ℕ) c).obj (F.obj (K.homology c))) c)) :=
    hG _ (CohomologyConcentration.projection_quasiIso _ c
      (fun q hq => exactAt_single_obj (.up ℕ) c (F.obj (K.homology c)) q hq))
  let : IsIso (G.map (CohomologyConcentration.projection ((single D (.up ℕ) c).obj N) c)) :=
    hG _ (CohomologyConcentration.projection_quasiIso _ c (fun q hq => exactAt_single_obj (.up ℕ) c N q hq))
  exact ConcentrationZigzagSingle.map_to_single G FK FS FT c p i (F.obj (K.homology c))
    ((singleMapHomologicalComplex F (.up ℕ) c).hom.app (K.homology c))
    ((K.sc c).mapHomologyIso F) (ConcentrationHomology.inclusion F K c) N a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.FunctorConcentration
