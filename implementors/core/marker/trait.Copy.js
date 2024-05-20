(function() {var implementors = {
"halo2_backend":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/poly/struct.Coeff.html\" title=\"struct halo2_backend::poly::Coeff\">Coeff</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_backend/helpers/enum.SerdeFormat.html\" title=\"enum halo2_backend::helpers::SerdeFormat\">SerdeFormat</a>"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>, T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/transcript/struct.ChallengeScalar.html\" title=\"struct halo2_backend::transcript::ChallengeScalar\">ChallengeScalar</a>&lt;C, T&gt;<span class=\"where fmt-newline\">where\n    C::Scalar: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</span>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/poly/struct.ExtendedLagrangeCoeff.html\" title=\"struct halo2_backend::poly::ExtendedLagrangeCoeff\">ExtendedLagrangeCoeff</a>"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/transcript/struct.Challenge255.html\" title=\"struct halo2_backend::transcript::Challenge255\">Challenge255</a>&lt;C&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/poly/struct.LagrangeCoeff.html\" title=\"struct halo2_backend::poly::LagrangeCoeff\">LagrangeCoeff</a>"],["impl&lt;F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_backend/poly/commitment/struct.Blind.html\" title=\"struct halo2_backend::poly::commitment::Blind\">Blind</a>&lt;F&gt;"]],
"halo2_frontend":[["impl&lt;F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + Field&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_frontend/dev/enum.CellValue.html\" title=\"enum halo2_frontend::dev::CellValue\">CellValue</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/struct.Instance.html\" title=\"struct halo2_frontend::plonk::circuit::Instance\">Instance</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.InstanceQuery.html\" title=\"struct halo2_frontend::plonk::circuit::expression::InstanceQuery\">InstanceQuery</a>"],["impl&lt;F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_frontend/plonk/assigned/enum.Assigned.html\" title=\"enum halo2_frontend::plonk::assigned::Assigned\">Assigned</a>&lt;F&gt;"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + <a class=\"trait\" href=\"halo2_frontend/plonk/circuit/trait.ColumnType.html\" title=\"trait halo2_frontend::plonk::circuit::ColumnType\">ColumnType</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.Column.html\" title=\"struct halo2_frontend::plonk::circuit::expression::Column\">Column</a>&lt;C&gt;"],["impl&lt;V: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/circuit/struct.Value.html\" title=\"struct halo2_frontend::circuit::Value\">Value</a>&lt;V&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/circuit/struct.Cell.html\" title=\"struct halo2_frontend::circuit::Cell\">Cell</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/sealed/struct.Phase.html\" title=\"struct halo2_frontend::plonk::circuit::expression::sealed::Phase\">Phase</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.FixedQuery.html\" title=\"struct halo2_frontend::plonk::circuit::expression::FixedQuery\">FixedQuery</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.Selector.html\" title=\"struct halo2_frontend::plonk::circuit::expression::Selector\">Selector</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.Challenge.html\" title=\"struct halo2_frontend::plonk::circuit::expression::Challenge\">Challenge</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/struct.Fixed.html\" title=\"struct halo2_frontend::plonk::circuit::Fixed\">Fixed</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.TableColumn.html\" title=\"struct halo2_frontend::plonk::circuit::expression::TableColumn\">TableColumn</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/circuit/struct.RegionIndex.html\" title=\"struct halo2_frontend::circuit::RegionIndex\">RegionIndex</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/circuit/struct.RegionStart.html\" title=\"struct halo2_frontend::circuit::RegionStart\">RegionStart</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/expression/struct.AdviceQuery.html\" title=\"struct halo2_frontend::plonk::circuit::expression::AdviceQuery\">AdviceQuery</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_frontend/circuit/layouter/enum.RegionColumn.html\" title=\"enum halo2_frontend::circuit::layouter::RegionColumn\">RegionColumn</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/struct.Advice.html\" title=\"struct halo2_frontend::plonk::circuit::Advice\">Advice</a>"]],
"halo2_middleware":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_middleware/circuit/struct.ChallengeMid.html\" title=\"struct halo2_middleware::circuit::ChallengeMid\">ChallengeMid</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_middleware/poly/struct.Rotation.html\" title=\"struct halo2_middleware::poly::Rotation\">Rotation</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_middleware/circuit/struct.ColumnMid.html\" title=\"struct halo2_middleware::circuit::ColumnMid\">ColumnMid</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_middleware/circuit/enum.VarMid.html\" title=\"enum halo2_middleware::circuit::VarMid\">VarMid</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"enum\" href=\"halo2_middleware/circuit/enum.Any.html\" title=\"enum halo2_middleware::circuit::Any\">Any</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"halo2_middleware/circuit/struct.QueryMid.html\" title=\"struct halo2_middleware::circuit::QueryMid\">QueryMid</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()