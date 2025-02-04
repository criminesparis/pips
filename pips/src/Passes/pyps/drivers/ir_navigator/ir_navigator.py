import os
import re
import shutil
import webbrowser

from pyps import module
from pypsutils import get_runtimedir


def ir_navigator(m, openBrowser=False, output_dir='ir_navigator', keep_existing=False, symbol_table=False):
    """
    Produce IR (internal representation) output for a module
    """
    m.html_prettyprint(symbol_table=symbol_table)
    filename = os.path.join(m.workspace.dirname, m.show('HTML_IR_FILE'))

    if not os.path.isfile(filename):
        raise RuntimeError('File (' + filename + ") doesn't exist! Bug inside ?")

    read_data = open(filename).read()

    # Create output dir if not existing    
    if not os.path.isdir(output_dir):
        os.makedirs(output_dir)

    # Initialize output directory
    ir_navigator_runtime_dir = get_runtimedir('ir_navigator')

    for f in os.listdir(ir_navigator_runtime_dir):
        shutil.copy(os.path.join(ir_navigator_runtime_dir, f), os.path.join(output_dir, f))

    # Templating
    read_template = open(os.path.join(output_dir, 'template.html')).read()
    read_data = re.sub('INCLUDE_RI_HERE', read_data, read_template)

    # writing the output file
    output_file = ''
    current_suffix = ''
    while output_file == '':
        try_output_file = os.path.join(output_dir, m.name + str(current_suffix) + '.html')
        if not keep_existing or not os.path.exists(try_output_file):
            output_file = try_output_file
        else:
            if current_suffix == '':
                current_suffix = 1
            else:
                current_suffix += 1

    with open(output_file, 'w') as f:
        f.write(read_data)

    # Open a web browser if requested
    if openBrowser:
        webbrowser.open(output_file)


module.ir_navigator = ir_navigator
