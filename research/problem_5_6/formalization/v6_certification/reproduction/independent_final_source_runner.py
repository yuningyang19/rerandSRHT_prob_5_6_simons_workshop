import pathlib,tarfile,hashlib,json,subprocess,os,time,datetime,sys
assert len(sys.argv)==5, 'usage: runner COMMIT ARCHIVE_SHA256 ARCHIVE_BASENAME OUTPUT_SLUG'
commit,expected_sha,archive_name,slug=sys.argv[1:]
assert len(commit)==40 and len(expected_sha)==64 and all(c in '0123456789abcdef' for c in commit+expected_sha)
assert pathlib.Path(archive_name).name==archive_name and all(c.isalnum() or c in '-_' for c in slug)
R=pathlib.Path('/Users/yuningyang/GitHub/rsvd_essential_v6_certification');E=R/'research/problem_5_6/formalization/v6_certification';archive=E/'packages'/archive_name;dest=E/'packages'/('cold-'+slug);report=E/'reproduction'/('independent_final_source_cold_'+slug+'.json');log=report.with_suffix('.log')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
assert sha(archive)==expected_sha;assert not dest.exists();started=time.monotonic();record={'status':'RUNNING','started_utc':utc(),'verification_commit':commit,'archive_sha256':expected_sha,'archive':str(archive),'destination':str(dest),'destination_was_absent':True,'execution_method':'Validate the exact new archive, unpack into a previously absent directory, shallow-fetch only exact official dependency source revisions, verify zero compiled objects, then invoke the archive documented run_suite.py exactly once. This is a new corrected-entrypoint test; prior c030 failures and recovery remain separate.','compiled_cache_reused':False,'global_git_config_modified':False,'source_fetches':[]}
def save():report.write_text(json.dumps(record,indent=2)+'\n')
env=os.environ.copy();i=int(env.get('GIT_CONFIG_COUNT','0'));env['GIT_CONFIG_COUNT']=str(i+1);env[f'GIT_CONFIG_KEY_{i}']='http.version';env[f'GIT_CONFIG_VALUE_{i}']='HTTP/1.1';env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env['PYTHONDONTWRITEBYTECODE']='1';record['child_git_http_version']=subprocess.check_output(['/usr/bin/git','config','--get','http.version'],env=env,text=True).strip();assert record['child_git_http_version']=='HTTP/1.1'
compiled={'.olean','.ilean','.pyc','.o','.a','.so','.dylib','.dll','.exe'}
def run(cmd,cwd,out):
 r={'command':cmd,'cwd':str(cwd),'started_utc':utc()};record['current_command']=r;save();out.write((json.dumps(r)+'\n').encode());out.flush();t=time.monotonic();p=subprocess.run(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT);r.update(returncode=p.returncode,elapsed_seconds=time.monotonic()-t,ended_utc=utc());record.setdefault('execution_commands',[]).append(r);save()
 if p.returncode:raise subprocess.CalledProcessError(p.returncode,cmd)
try:
 save()
 with tarfile.open(archive,'r:gz') as tar:
  members=tar.getmembers();names=[m.name for m in members];assert len(names)==len(set(names))
  for m in members:
   p=pathlib.PurePosixPath(m.name);assert m.isfile() and not p.is_absolute() and '..' not in p.parts and '.lake' not in p.parts and '__pycache__' not in p.parts and p.suffix not in compiled
  dest.mkdir(parents=True)
  for m in members:
   p=dest/m.name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(tar.extractfile(m).read())
 manifest=json.loads((dest/'EXPORT_MANIFEST.json').read_text());assert manifest['verification_commit']==record['verification_commit'];assert set(names)==set(manifest['files'])|{'README.md','EXPORT_MANIFEST.json'}
 for name,h in manifest['files'].items():assert sha(dest/name)==h,name
 entry='research/problem_5_6/formalization/v6_certification';assert (dest/'README.md').read_bytes()==(dest/entry/'README.md').read_bytes();L=dest/'research/problem_5_6/formalization/lean';assert not (L/'.lake').exists();record.update(archive_members=len(names),source_members_checked=len(manifest['files']),initial_compiled_objects=0,archive_validation='PASS');save()
 dependencies=json.loads((L/'lake-manifest.json').read_text());pk=L/dependencies['packagesDir'];pk.mkdir(parents=True)
 with log.open('wb') as out:
  for dep in dependencies['packages']:
   d=pk/dep['name'];d.mkdir();run(['/usr/bin/git','init'],d,out);run(['/usr/bin/git','remote','add','origin',dep['url']],d,out);run(['/usr/bin/git','-c','gc.auto=0','fetch','--depth','1','origin',dep['rev']],d,out);run(['/usr/bin/git','checkout','--detach','FETCH_HEAD'],d,out);head=subprocess.check_output(['/usr/bin/git','rev-parse','HEAD'],cwd=d,text=True).strip();assert head==dep['rev'];dirty=subprocess.check_output(['/usr/bin/git','status','--porcelain','--untracked-files=no'],cwd=d,text=True).strip();assert not dirty;record['source_fetches'].append({'name':dep['name'],'url':dep['url'],'expected_revision':dep['rev'],'actual_revision':head,'tracked_source_clean':True,'source_only_shallow_fetch':True});save()
  objects=[str(p.relative_to(dest)) for p in dest.rglob('*') if p.is_file() and p.suffix in compiled];assert not objects,objects[:10];record['prebuild_compiled_objects']=len(objects);record['source_acquisition_elapsed_seconds']=time.monotonic()-started;save();run(['python3',entry+'/scripts/run_suite.py'],dest,out)
 record.update(status='PASS',returncode=0,documented_run_suite_completed_without_recovery=True)
except Exception as exc:
 record.update(status='FAIL',returncode=getattr(exc,'returncode',1),error=str(exc))
finally:
 if 'manifest' in locals():record['changed_proof_or_build_inputs']=[name for name,h in manifest['files'].items() if name.startswith('research/problem_5_6/formalization/lean/') and (not (dest/name).is_file() or sha(dest/name)!=h)]
 if record.get('changed_proof_or_build_inputs'):record.update(status='FAIL',returncode=1)
 record.update(ended_utc=utc(),elapsed_seconds=time.monotonic()-started,raw_log=str(log),raw_log_sha256=sha(log) if log.exists() else None);save();print(json.dumps(record,indent=2));sys.exit(record['returncode'])
