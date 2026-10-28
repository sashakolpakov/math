import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ProductModelCycleLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ResidueModelCycle
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair

/-! # Product Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductFrame

noncomputable section

/-! A line bundle on a varying product of projective abelian schemes
over a Noetherian local affine base is trivial when its two axes and
coefficient-residue fiber are trivial. The base may be nonreduced. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
variable {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable [A.scheme.left.IsSeparated] [B.scheme.left.IsSeparated]
variable [(pullback A.scheme.hom B.scheme.hom).IsSeparated]
variable (PA : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)))
variable {ι κ : Type u} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → A.scheme.left.Opens) (V : κ → B.scheme.left.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sA : S ⟶ A.scheme.left) (hsA : sA ≫ A.scheme.hom = 𝟙 _)
variable (sB : S ⟶ B.scheme.left) (hsB : sB ≫ B.scheme.hom = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sA ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sB ⁻¹ᵁ V j₀)
variable (L : Line.Bundles.LineBundle (pullback A.scheme.hom B.scheme.hom))
variable (eA : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left A.scheme.hom B.scheme.hom sB hsB)).sheaf ≅
  Line.Bundles.structureModule A.scheme.left)
variable (eB : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right A.scheme.hom B.scheme.hom sA hsA)).sheaf ≅
  Line.Bundles.structureModule B.scheme.left)

include PA PB P hU hV hcU hcV eA eB i₀ hi₀ j₀ hj₀

theorem localAbelianProduct_line_trivial
    (he : (L.pullback (pullback.fst (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
      (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))).sheaf ≅
        Line.Bundles.structureModule (pullback (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
          (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule (pullback A.scheme.hom B.scheme.hom)) := by
  classical
  let : LinearOrder (Σ _ : ι, κ) := (Fintype.equivFin (Σ _ : ι, κ)).linearOrder
  let W := Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover A.scheme.hom B.scheme.hom U V
  let π := pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom
  have hW : iSup W = ⊤ := Quotients.FiniteDescent.ProductCech.Construction.ProductCechCoverProperties.covers _ _ U V hcU hcV
  have haW : ∀ i, IsAffineOpen (W i) := Quotients.FiniteDescent.ProductCech.Construction.ProductCechCoverProperties.affine _ _ U V hU hV
  have : IsProper π := inferInstance
  have : Smooth π := inferInstance
  have : GeometricallyConnected π :=
    GeometricallyConnected.comp (pullback.fst A.scheme.hom B.scheme.hom) A.scheme.hom
  obtain ⟨D, φ, hq, ⟨N, hN⟩, hfin, hproj, hφ⟩ :=
    Quotients.FiniteDescent.AffineCoverModel.Construction.AffineCoverPerfectModel.exists_model π P W hW haW L
  have : QuasiIso φ := hq
  have : ∀ n, Module.Finite Γ(S, ⊤) (D.X n) := hfin
  have : ∀ n, Module.Projective Γ(S, ⊤) (D.X n) := hproj
  let q := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (pullback.fst π q) π
      (pullback.snd π q) q pullback.condition L.sheaf W φ) :=
    Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso (pullback.fst π q) π (pullback.snd π q)
      q L.sheaf W φ (IsPullback.of_hasPullback π q)
      (fun n i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection W haW n i.1) hφ
  have : ConnectedSpace (pullback π q : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd π q)
  have : IsIntegral (pullback π q) :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral (pullback.snd π q)
  have : IsIntegral (Over.mk (pullback.snd π q)).left :=
    inferInstanceAs (IsIntegral (pullback π q))
  have : IsProper (Over.mk (pullback.snd π q)).hom :=
    inferInstanceAs (IsProper (pullback.snd π q))
  have : Nontrivial Γ((Scheme.Modules.pullback (pullback.fst π q)).obj L.sheaf, ⊤) :=
    Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality.nontrivial_sections_of_trivial (Over.mk (pullback.snd π q))
      (L.pullback (pullback.fst π q)) he
  have hn := (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections (pullback.fst π q) π
    (pullback.snd π q) q pullback.condition L.sheaf W hW φ).nontrivial_congr.mpr
      (show Nontrivial Γ((Scheme.Modules.pullback (pullback.fst π q)).obj L.sheaf, ⊤)
        from inferInstance)
  have hlift := Abelian.ProductModelCycleLifting.abelianProductModel_residue_cycle_lift A B PA PB U V hU hV hcU hcV
    sA hsA sB hsB i₀ hi₀ j₀ hj₀ L eA eB φ N hN hφ he
  obtain ⟨x, hx, hxn⟩ := Coefficient.ResidueModelCycle.extendedComplex_exists_surviving_cycle D q.appTop.hom
    (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldSectionsEquiv S (IsLocalRing.ResidueField Γ(S, ⊤)))
    (Coefficient.ResidueModelCycle.coefficientSectionsEquiv_one S (IsLocalRing.ResidueField Γ(S, ⊤))) hn hlift
  let z : (D.d 0 1).hom.ker := ⟨x, hx⟩
  have hz : (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle q z).val ≠ 0 := hxn
  exact Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood.Construction.ModelFrameNeighborhood.exists_global_frame_of_coefficient_residue π L W hW φ
    (pullback.fst π q) (pullback.snd π q) (IsPullback.of_hasPullback π q) ⟨he⟩ inferInstance z hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductFrame
