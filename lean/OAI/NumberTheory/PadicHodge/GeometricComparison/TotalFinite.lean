import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.InverseHom
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Total Finite -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.TotalFinite.FiniteTotalExtensionNaturality

/-! Naturality of the total comparison after extending to the native integer grading. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive]

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

theorem naturality {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (φ : K ⟶ L) :
    HomologicalComplex.extendMap (total.map (Finite.TotalIso.FiniteTotalNaturality.map F φ) (.up ℕ))
        ComplexShape.embeddingUpNat ≫ (Finite.TotalIso.FiniteTotalExtension.iso F L).hom =
      (Finite.TotalIso.FiniteTotalExtension.iso F K).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap (total.map φ (.up ℕ)) ComplexShape.embeddingUpNat) := by
  let E := ComplexShape.embeddingUpNat.extendFunctor D
  have h₁ := congrArg E.map (Finite.TotalIso.FiniteTotalNaturality.naturality F φ)
  simp only [Functor.map_comp] at h₁
  have h₂ := InverseHom.InverseHomCongr.inverse_square
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (K.total (.up ℕ)))
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (L.total (.up ℕ))) _ _
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality F ComplexShape.embeddingUpNat (total.map φ (.up ℕ))).symm
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end NumberTheory.PadicHodge.GeometricComparison.TotalFinite.FiniteTotalExtensionNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.TotalFinite.IntegerTotalFunctor

/-! The actual finite-diagonal total complex, extended to integers, as a functor. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def functor : HomologicalComplex₂ C (.up ℕ) (.up ℕ) ⥤ CochainComplex C ℤ :=
  totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor C

variable {C} {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive]

def scalarIso :
    (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ) ⋙ functor D ≅
      functor C ⋙ F.mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (Finite.TotalIso.FiniteTotalExtension.iso F)
    (fun {_ _} φ => FiniteTotalExtensionNaturality.naturality F φ)

end NumberTheory.PadicHodge.GeometricComparison.TotalFinite.IntegerTotalFunctor

namespace NumberTheory.PadicHodge.GeometricComparison.TotalFinite.TotalScalarComparison

/-! Transport a bicomplex scalar isomorphism through the canonical integer total comparison. -/

open _root_.CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive]

def iso {K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    {L : HomologicalComplex₂ D (.up ℕ) (.up ℕ)} (e : ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K ≅ L) :
    (F.mapHomologicalComplex (.up ℤ)).obj ((IntegerTotalFunctor.functor C).obj K) ≅ (IntegerTotalFunctor.functor D).obj L :=
  ((IntegerTotalFunctor.scalarIso F).app K).symm ≪≫ (IntegerTotalFunctor.functor D).mapIso e

theorem naturality {K K' : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    {L L' : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
    (e : ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K ≅ L) (e' : ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K' ≅ L') (φ : K ⟶ K') (ψ : L ⟶ L')
    (h : ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).map φ ≫ e'.hom = e.hom ≫ ψ) :
    (F.mapHomologicalComplex (.up ℤ)).map ((IntegerTotalFunctor.functor C).map φ) ≫ (iso F e').hom =
      (iso F e).hom ≫ (IntegerTotalFunctor.functor D).map ψ := by
  have h₁ := (IntegerTotalFunctor.scalarIso F).inv.naturality φ
  have h₂ := congrArg (IntegerTotalFunctor.functor D).map h
  simp only [Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end NumberTheory.PadicHodge.GeometricComparison.TotalFinite.TotalScalarComparison

end

end OAI
