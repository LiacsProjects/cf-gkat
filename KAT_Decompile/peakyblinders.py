import subprocess
import glob
import os
import sys

if __name__ == "__main__":
    coreutilssrc = sys.argv[1]
    KATsrc = sys.argv[2]
    output = sys.argv[3]
    report = sys.argv[4]
    includedirs = [subprocess.check_output(["clang", "--print-file-name=include"], universal_newlines=True).strip(), subprocess.check_output(["gcc", "--print-file-name=include"], universal_newlines=True).strip(), os.path.join(coreutilssrc, "src"), os.path.join(coreutilssrc, "lib")]

    if not os.path.exists(os.path.join(output, "src")):
        if not os.path.exists(output):
            os.mkdir(output)

        os.mkdir(os.path.join(output, "src"))

    with open(report, 'w') as reportcsv:
        print("filename,function,blinded,indicator", file=reportcsv)

        for i in glob.glob("%s/*.c" % os.path.join(coreutilssrc, "src")):
            b = os.path.join(output, "src", os.path.basename(i))

            with open(b, 'w') as blinded:
                with subprocess.Popen([os.path.join(KATsrc, "_build/default/frontend/blinder.exe"), "--clang", "%s -isystem frontend" % " ".join(["-I %s" % d for d in includedirs]), i], stdout=blinded, stderr=subprocess.PIPE, universal_newlines=True) as blinder:
                    _, stderr_data = blinder.communicate()

                    if blinder.returncode == 0:
                        for l in stderr_data.splitlines():
                            if l.startswith("blinder - "):
                                print(l[len("blinder - "):], file=reportcsv)

                        o = "%s.o" % os.path.splitext(b)[0]

                        blinded.close()
                        subprocess.Popen(["clang", "-isystem", "frontend", "-o", o, "-c", b], stderr=subprocess.DEVNULL)

            reportcsv.flush()
            subprocess.check_output(["clang-format", "-i", b])
