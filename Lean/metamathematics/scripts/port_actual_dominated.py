#!/usr/bin/env python3
"""Same hash-pinned generic proof templates, instantiated in the NEW actual fragment.
No historical Derivation is imported or converted. Lean checks emitted Proof terms.
"""
import pathlib,subprocess,sys,tempfile
with tempfile.TemporaryDirectory() as d:
    intermediate=pathlib.Path(d)/'Generic.lean'
    subprocess.run([sys.executable,str(pathlib.Path(__file__).with_name('port_dominated_core.py')),
                    sys.argv[1],str(intermediate)],check=True)
    text=intermediate.read_text()
text=text.replace('import PA215PA.NativeDecode','import PA215PA.ActualCore')
text=text.replace('PA215.PA.NativeCalculus.Dominated','PA215.PA.NativeCalculus.ActualCore.Dominated')
text=text.replace('Derivation','Proof')
text=text.replace('NumericDecode.pair_bounds','PA215.Source.Enumeration.pair_bounds')
text=text.replace('finite dominated native derivation','finite actual-fragment proof')
pathlib.Path(sys.argv[2]).write_text(text)
