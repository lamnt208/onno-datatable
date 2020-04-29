# onno-datatable
=======
# onno-datatable

> Made with create-react-library

[![NPM](https://img.shields.io/npm/v/onno-datatable.svg)](https://www.npmjs.com/package/onno-datatable) [![JavaScript Style Guide](https://img.shields.io/badge/code_style-standard-brightgreen.svg)](https://standardjs.com)

## Install

```bash
npm install --save onno-datatable
```

## Usage

```jsx
import React, { Component } from 'react'

import Table, { Column } from 'onno-datatable'
import 'onno-datatable/dist/index.css'

class Example extends Component {
  render() {
    return <Table
				data={teams}
				filterable={true}
			>
				<Column label="Name" field="name" sortable={true} />
				<Column label="Status" field="enable" sortable={true} render={(each) => each.enable === 'Yes' ?
					(<Badge variant="success">Enabled</Badge>) :
					(<Badge variant="danger">Disabled</Badge>)} />
				<Column label="Action" hidden={!userInfo.isAdmin} render={(each) => (
					<>
						<a href="javascript:void(0)" className="mr-2 small" onClick={this.onChangeStatus(each)}>
							{each.enable === 'Yes' ?
								(<span className="text-danger"><i className="fas fa-trash-alt"></i> Disabled </span>) :
								(<span className="text-success"><i className="fas fa-eye"></i> Enable </span>)}
						</a>
						<a className="text-secondary small" onClick={this.onOpenEditForm(each)} href="javascript:void(0)">
							<i className="fas fa-edit"></i> Edit
									</a>
					</>
				)} />
			</Table>
  }
}
```

## License

MIT © [lamnt.it@gmail.com](https://github.com/lamnt208)
