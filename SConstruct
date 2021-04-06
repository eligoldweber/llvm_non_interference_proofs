  
# -*- python -*-
import atexit
import os, os.path
import re
import shutil
import subprocess
import sys
import SCons.Util
import threading

Import("*")

env = Environment(ENV=os.environ)

AddOption('--dafny-path',
  dest='dafny_path',
  type='string',
  default=None,
  action='store',
  help='Specify the path to Dafny tool binaries')

AddOption('--no-verify',
  dest='no_verify',
  default=False,
  action='store_true',
  help="Don't verify, just build executables")

AddOption('--time-limit',
  dest='time_limit',
  type='int',
  default=30,
  action='store',
  help='Specify the time limit to use for each verification')

AddOption('--verify-root',
  dest='verify_root',
  type='string',
  default=None,
  action='store',
  help='Optionally specify a .dfy file to verify (along with all dependencies)')

verify_root = GetOption('verify_root')
dafny_path = GetOption('dafny_path')
if dafny_path is None:
  sys.stderr.write("ERROR:  Missing --dafny-path on command line\n")
  exit(-1)

if sys.platform == "win32" or sys.platform == "cygwin":
  dafny_exe = os.path.join(dafny_path, 'Dafny.exe')
  if not os.path.exists(dafny_exe):
    print("ERROR:  Could not find Dafny executable in " + dafny_path)
    exit(-1)
  dafny_invocation = [dafny_exe]
else:
  dafny_exe = os.path.join(dafny_path, 'Dafny.dll')
  if not os.path.exists(dafny_exe):
    dafny_exe = os.path.join(dafny_path, 'dafny.dll')
  if not os.path.exists(dafny_exe):
    print("ERROR:  Could not find Dafny executable in " + dafny_path)
    exit(-1)
  dafny_invocation = ["dotnet", dafny_exe]

# Useful Dafny command lines
dafny_basic_args = ['/compile:0', '/timeLimit:' + str(GetOption('time_limit')), '/trace']
dafny_default_args = dafny_basic_args + ['/arith:5', '/noCheating:1']
dafny_args_nlarith = dafny_basic_args + ['/arith:2', '/noCheating:1']
dafny_spec_args = dafny_basic_args

####################################################################
#
#   General routines
#
####################################################################

def recursive_glob(env, pattern, strings=False):
  matches = []
  split = os.path.split(pattern) # [0] is the directory, [1] is the actual pattern
  platform_directory =  split[0] #os.path.normpath(split[0])
  for d in os.listdir(platform_directory):
    if os.path.isdir(os.path.join(platform_directory, d)):
      newpattern = os.path.join(split[0], d, split[1])
      matches.append(recursive_glob(env, newpattern, strings))

  files = env.Glob(pattern, strings=strings)
  matches.append(files)
  return Flatten(matches)

####################################################################
#
#   Make table of special cases requiring non-default arguments
#
####################################################################

source_to_args = [
  ('.*Dafny\/Libraries\/math\/[^\.]+nonlinear\.i\.dfy', dafny_args_nlarith),
  ('.*Dafny\/Libraries\/math\/[^\.]+auto[^\.]*\.i\.dfy', dafny_default_args),
  ('.*Dafny\/Libraries\/math\/mul\.i\.dfy', dafny_args_nlarith),
  ('.*\.dfy', dafny_default_args),
]

####################################################################
#
#   Dafny-specific utilities
#
####################################################################

dafny_include_re = re.compile(r'include\s+"(\S+)"', re.M)
single_line_comments_re = re.compile(r'//.*\n')
multiline_comments_re = re.compile(r'/\*(([^/\*])|(\*[^/])|(/[^\*]))*\*/')

def remove_dafny_comments(contents):
  # Strip out multi-line comments, using a loop to deal with nested comments
  while True:
    (contents, substitutions_made) = re.subn(multiline_comments_re, ' ', contents)
    if substitutions_made == 0:
      break

  # Strip out single-line comments
  contents = re.sub(single_line_comments_re, '\n', contents)
  return contents

# helper to look up Dafny command-line arguments matching a srcpath, from the
# source_to_args[] dictionary, dealing with POSIX and Windows pathnames, and
# falling back on a default if no specific override is present.
def get_dafny_command_line_args(srcpath):
  srcpath = os.path.normpath(srcpath)  # normalize the path, which, on Windows, switches to \\ separators
  srcpath = srcpath.replace('\\', '/') # switch to posix path separators
  for entry in source_to_args:
    pattern, args = entry
    if re.search(pattern, srcpath, flags=re.IGNORECASE):
      return args

  return dafny_default_args

dependencies_by_file = dict()
already_verified_files = set()
already_printed_files = set()

# Scan a .dfy file to discover its transitive dependencies, and store a
# list of them in dependencies_by_file[fullpath].
def recursively_scan_for_dependencies(fullpath, depth):
  if fullpath in dependencies_by_file:
    return
  contents = File(fullpath).get_text_contents()
  dirname = os.path.dirname(fullpath)
  filename = os.path.basename(fullpath)
  contents = remove_dafny_comments(contents)
  includes = dafny_include_re.findall(contents)
  extra_files = [os.path.abspath(os.path.join(dirname, i)) for i in includes]
  transitive_dependencies = set(extra_files)
  for srcpath in extra_files:
    recursively_scan_for_dependencies(srcpath, depth + 1)
    transitive_dependencies.update(dependencies_by_file[srcpath])
  all_dependencies = sorted(list(transitive_dependencies))
  dependencies_by_file[fullpath] = all_dependencies


# Scan a .dfy file to discover its dependencies, and add .vdfy targets for each.
def scan_for_more_targets(target, source, env):
  node = source[0]
  fullpath = str(node)
  recursively_scan_for_dependencies(fullpath, 0)
  dependencies = dependencies_by_file[fullpath]
  for srcpath in dependencies:
    if srcpath not in already_verified_files:
      f = os.path.splitext(srcpath)[0] + '.vdfy'
      env.DafnyVerify(f, [srcpath, dafny_exe])
      already_verified_files.add(srcpath)
  return target, source + dependencies

####################################################################
#
#   Dafny routines
#
####################################################################

def check_dafny(lines):
  for line in lines:
    if re.search("[Oo]ut of resource", line):
      sys.stderr.write("Dafny reported an out-of-resource error\n")
      raise Exception()
    if re.search("proof obligations\]\s+errors", line):
      sys.stderr.write("Dafny reported errors not in summary\n")
      raise Exception()

def check_and_print_tail(filename):
  with open(filename, 'r') as fh:
    lines = fh.readlines()
    check_dafny(lines)
    sys.stdout.write(lines[-1])
    sys.stdout.write('Full check of Dafny output succeeded\n')

CheckAndPrintTail = SCons.Action.ActionFactory(check_and_print_tail, lambda x: "Checking " + x)

def generate_dafny_verifier_actions(source, target, env, for_signature):
  abs_source = File(source[0]).abspath
  abs_target = File(target[0]).abspath
  source_name = str(source[0])
  # print("generate_dafny_verifier_actions " + str(dafny_invocation))
  temp_target_file = re.sub(r'\.dfy$', '.tmp', source_name)
  args = get_dafny_command_line_args(abs_source)
  # temp = [source_name, ">", temp_target_file]
  # print ("temp " + str(temp))
  return [
      dafny_invocation + args + [source_name, ">", temp_target_file],
      CheckAndPrintTail(temp_target_file),
      Move(abs_target, temp_target_file)
  ]

# Add env.DafnyVerify(), to generate Dafny verifier actions
def add_dafny_verifier_builder(env):
  dafny_verifier = Builder(generator = generate_dafny_verifier_actions,
                           suffix = '.vdfy',
                           src_suffix = '.dfy',
                           chdir=0,
                           emitter = scan_for_more_targets,
                           )
  env.Append(BUILDERS = {'DafnyVerify' : dafny_verifier})

# Verify a set of Dafny files by creating verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_dafny_files(env, files):
  for f in files:
    target = os.path.splitext(f)[0] + '.vdfy'
    env.DafnyVerify(target, [f, dafny_exe])

# Verify *.dfy files in a list of directories.  This enumerates
# all files in those trees, and creates verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_files_in(env, directories):
  for d in directories:
    files = recursive_glob(env, d+'/*.dfy', strings=True)
    verify_dafny_files(env, files)

def verify_dafny_file(source):
  # if GetOption('no_verify'):
  #   return
  target = re.sub(r"\.dfy$", ".vdfy", source)
  env.DafnyVerify(target, [source, dafny_exe])

  ####################################################################
#
#   Extract verification failure information
#
####################################################################

# extract a string filename out of a build failure
def bf_to_filename(bf):
  import SCons.Errors
  if bf is None: # unknown targets product None in list
    return '(unknown tgt)'
  elif isinstance(bf, SCons.Errors.StopError):
    return str(bf)
  elif bf.node:
    return str(bf.node)
  elif bf.filename:
    return bf.filename
  return '(unknown failure)'

def report_verification_failures():
  from SCons.Script import GetBuildFailures
  bf = GetBuildFailures()
  if bf:
    # bf is normally a list of build failures; if an element is None,
    # it's because of a target that scons doesn't know anything about.
    for x in bf:
      if x is not None:
        filename = bf_to_filename(x)
        if filename.endswith('.vdfy'):
          file_to_print = os.path.splitext(filename)[0] + '.tmp'
          if os.path.isfile(file_to_print):
            sys.stdout.write('\n##### Verification error.  Printing contents of ' + file_to_print + ' #####\n\n')
            with open (file_to_print, 'r') as myfile:
              sys.stdout.write(myfile.read())
          else:
            print("ERROR:  Verification error, but cannot print output since file %s doesn't exist" % (file_to_print))
        else:
          print("Build failure for %s" % (filename))


def display_build_status():
  report_verification_failures()


####################################################################
#
#   Put it all together
#
####################################################################

add_dafny_verifier_builder(env)
env.AddMethod(verify_files_in, "VerifyFilesIn")
env.AddMethod(verify_dafny_files, "VerifyDafnyFiles")
atexit.register(display_build_status)


####################################################################
#
#   Create dependencies & Verify
#
####################################################################

def run_directory(dir_name, dafny_files):
  for dafny_file in dafny_files:
    source = "%s/%s.i.dfy" % (dir_name, dafny_file)
    target = "%s/%s.i.vdfy" % (dir_name, dafny_file)
    env.DafnyVerify(target, [source, dafny_exe])


if verify_root is None:
  print("==> No .dfy root specified, verifying all .dfy files in Dafny/examples folder")
  run_directory('Dafny/examples',["challengeProblem1Simplified",
                                      "sextchallengeProblem1Simplified",
                                      "simple",
                                      "generalInstructions"])
else:
  verify_dafny_file(str(GetOption('verify_root')))

